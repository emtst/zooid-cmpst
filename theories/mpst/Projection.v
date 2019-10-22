From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Atom.
Require Import MPST.Role.
Require Import MPST.Forall.
Require Import MPST.LNVar.
Require Import MPST.Global.
Require Import MPST.Local.

Section Project.

  Definition ml_send p t L :=
    match L with
    | None => None
    | Some L => Some (l_send p t L)
    end.

  Definition ml_recv p t L :=
    match L with
    | None => None
    | Some L => Some (l_recv p t L)
    end.

  Definition project_msg (p : g_prefix) (r : role) (L : option l_ty) :=
    let: ((p, q), t) := p in
    if p == q
    then None
    else if p == r
         then ml_send q t L
         else if q == r
              then ml_recv p t L
              else L.

  Definition pproj_msg (p : g_prefix) (r1 r2 : role) (L : option s_ty) :=
    let: ((p, q), t) := p in
    if p == q
    then None
    else if (p == r1) && (q == r2)
         then ms_send t L
         else if (q == r1) && (p == r2)
              then ms_recv t L
              else L.

  Definition ml_brn (r : role) (a : seq (lbl * option l_ty)) :=
    match flat_alts a with
    | Some x => Some (l_brn r x)
    | None => None
    end.

  Definition ml_sel (r : role) (a : seq (lbl * option l_ty)) :=
    match flat_alts a with
    | Some x => Some (l_sel r x)
    | None => None
    end.

  Definition project_brn (p : g_prefix) (r : role) (K : seq (lbl * option l_ty)) :=
    let: ((p, q), t) := p in
    if p == q
    then None
    else if p == r
         then ml_sel q K
         else if q == r
              then ml_brn p K
              else merge_all K.

  Notation lbv n := (l_var (Rvar.bv n)).

  Definition p_proj (L : option l_ty) (r:role) :=
    match L with
    | Some l => partial_proj l r
    | None => None
    end.

  Definition ml_rec L :=
    match L with
    | Some L => if L == lbv 0 then None else Some (l_rec L)
    | None => None
    end.

  Fixpoint project (g : g_ty) (r : role) : option l_ty :=
    match g with
    | g_end => Some l_end
    | g_msg m G => project_msg m r (project G r)
    | g_var v => Some (l_var v)
    | g_rec G => let L := project G r in
                 if L == Some (lbv 0) then None else ml_rec L
    | g_brn p K =>
      let KL := map (fun X => (X.1, project X.2 r)) K in
      project_brn p r KL
    end.

  Lemma eta_option A (x : option A) :
    match x with
    | Some y => Some y
    | None => None
    end = x.
  Proof. by case: x. Qed.

  Lemma fun_option A B C (f : C -> B) (g : A -> C) (h : C) (x : option A) :
    f match x with
      | Some y => g y
      | None => h
      end = match x with
            | Some y => f (g y)
            | None => f h
            end.
  Proof. by case: x. Qed.

  Definition mdual l r :=
    match l, r with
    | Some L, Some L' => dual L L'
    | None, None => true
    | _, _ => false
    end.

  Notation sbv n := (s_var (Rvar.bv n)).

  Lemma pproj_rec L p:
    p_proj (ml_rec L) p = if p_proj L p == Some (sbv 0)
                          then None
                          else ms_rec (p_proj L p).
  Proof. by case: L=>//L/=; case: ifP=>[/eqP->|]. Qed.

  Lemma mdual_rec X Y :
    mdual (ms_rec X) (ms_rec Y) = mdual X Y.
  Proof. by case: X =>[X|]; case: Y=>[Y|]/=//. Qed.

  Lemma msrec_not_var S i : (ms_rec S == Some (sbv i)) = false.
  Proof. by case: S. Qed.

  Lemma pproj_recv f ty L p :
    p_proj (ml_recv f ty L) p =
    (if f == p then ms_recv ty (p_proj L p) else p_proj L p).
  Proof.
    rewrite /ml_recv (fun_option (fun X => p_proj X p)) /p_proj.
    by case: L=>[L|]/=; case: ifP=>//; rewrite eta_option.
  Qed.

  Lemma pproj_send f ty L p :
    p_proj (ml_send f ty L) p =
    (if f == p then ms_send ty (p_proj L p) else p_proj L p).
  Proof.
    rewrite /ml_send (fun_option (fun X => p_proj X p)) /p_proj.
    by case: L=>[L|]/=; case: ifP=>//; rewrite eta_option.
  Qed.

  Definition pproj_brn (p : g_prefix)
             (r1 r2 : role) (K : seq (lbl * option s_ty)) :=
    let: ((p, q), t) := p in
    if p == q
    then None
    else if (p == r1) && (q == r2)
         then ms_sel K
         else if (p == r2) && (q == r1)
              then ms_brn K
              else merge_all K.

  Lemma pproj_msg_swap pr p q L :
    p_proj (project_msg pr q L) p
    = pproj_msg pr q p (p_proj L p).
  Proof.
    case: pr=>[[f t] ty] /=.
    case: ifP =>// f_neq_t; case: ifP=>/=//[f_eq_g|f_neq_g].
    - case: ifP=>[/eqP->|t_neq_p].
      + by rewrite pproj_send eq_refl.
      + move: f_eq_g f_neq_t=>/eqP->.
        rewrite eq_sym=>->; rewrite /p_proj/=.
        by case: L=>//L/=; rewrite t_neq_p.
    - by case: ifP=>///=t_eq_q; rewrite pproj_recv.
  Qed.


  Lemma option_comm A B C (x : option A) (f : A -> option B) (g : B -> C) z z' :
    match
      match x with
      | Some y => f y
      | None => z
      end
    with
    | Some y => g y
    | None => z'
    end =
    match x with
    | Some y => match f y with
                    | Some y => g y
                    | None => z'
                end
    | None => match z with
              | Some y => g y
              | None => z'
              end
    end.
  Proof. by case: x. Qed.

  Lemma list_comm A B C (x : seq A) (f : A -> seq A -> option B) (g : B -> C) z z' :
    match
      match x with
      | y1 :: y2 => f y1 y2
      | [::] => z
      end
    with
    | Some y => g y
    | None => z'
    end =
    match x with
    | y1 :: y2 => match f y1 y2 with
                    | Some y => g y
                    | None => z'
                end
    | [::] => match z with
              | Some y => g y
              | None => z'
              end
    end.
  Proof. by case: x. Qed.


  Lemma flatten_some (A : eqType) (L : seq (lbl * option A)) LL :
    flatten L == Some LL ->
    L = [seq (X.1, Some X.2) | X <- LL].
  Proof.
    elim: L LL=>[LL /eqP-[<-]//| [l L] K Ih K']/=.
    case: L=>//a; move: Ih; case: (flatten K)=>//FK Ih /eqP-[<-]/=.
    by rewrite -Ih.
  Qed.

  Lemma flatalts_some (A : eqType) (L : seq (lbl * option A)) LL :
    flat_alts L == Some LL ->
    L = [seq (X.1, Some X.2) | X <- LL].
  Proof. by case: L=>// L K; apply: flatten_some. Qed.

  Lemma flatten_none (A : eqType) (L : seq (lbl * option A)) :
    flatten L == None -> exists l, (l, None) \in L.
  Proof.
    elim: L=>// [[l [S|]] K]/=.
    - move=> Ih F_none.
      have {F_none} /Ih: flatten K == None by case: (flatten K) F_none.
      + by move=>[l0 Pf]; exists l0; rewrite in_cons orbC Pf.
      + by move=>_ _; exists l; rewrite in_cons eq_refl.
  Qed.

  Lemma flatalts_none (A : eqType) (L : seq (lbl * option A)) :
    flat_alts L == None -> L == [::] \/ exists l, (l, None) \in L.
  Proof.
    case: L; first by move=> _; left.
    by move=> a L H; right; apply: flatten_none.
  Qed.

  Lemma flatten_pproj (L : seq (lbl * option l_ty)) t :
    flatten [seq (X.1, p_proj X.2 t) | X <- L]
    = match flatten L with
      | Some K => flatten [seq (X.1, partial_proj X.2 t) | X <- K]
      | None => None
      end.
  Proof.
    elim: L=>// [[l [S|]] K]///=.
    move=>->/=; rewrite option_comm/=.
    case: (partial_proj S t)=>[FK|]; last (by case: (flatten K)).
    by rewrite option_comm.
  Qed.

  Lemma flatalts_cons (A : eqType) (a : lbl * option A) L :
    flat_alts (a :: L) = flatten (a :: L).
  Proof. by []. Qed.

  Lemma flatalts_pproj (L : seq (lbl * option l_ty)) t :
    flat_alts [seq (X.1, p_proj X.2 t) | X <- L]
    = match flat_alts L with
      | Some K => flat_alts [seq (X.1, partial_proj X.2 t) | X <- K]
      | None => None
      end.
  Proof.
    case: L=>// a L; rewrite map_cons !flatalts_cons -map_cons flatten_pproj.
    case: {-1} (flatten (a::L)) (eq_refl (flatten (a::L)))=>// K.
    by move=>/flatten_some; case: K.
  Qed.

  Lemma pproj_sel f L t:
    p_proj (ml_sel f L) t =
    if f == t then ms_sel [seq (X.1, p_proj X.2 t) | X <- L]
    else merge_all [seq (X.1, p_proj X.2 t) | X <- L].
  Proof.
    rewrite /ml_sel (fun_option (fun X => p_proj X t))/=.
    move: {-1} (flat_alts L) (eq_refl (flat_alts L)) => LL.
    case: LL=>[LL|]; first by move=>/flatalts_some->; rewrite -map_comp /comp/=.
    case:ifP=> _//; rewrite /ms_sel.
    - by rewrite flatalts_pproj=>/eqP->.
    - move=>/flatalts_none-[/eqP->//|[l]].
      rewrite /merge_all; case: L=>// a K/=.
      case: a=>[l' [S|]]//.
      rewrite in_cons xpair_eqE andbC/=.
      case: (partial_proj S t)=>// {S}S.
      elim: K=>// [[l'' [S'|]] K]// Ih.
      rewrite in_cons xpair_eqE andbC/==>/Ih-{Ih}Ih.
      by case: (partial_proj S' t)=>// {S'}S'; case:ifP=>//.
  Qed.

  Lemma pproj_brn_swap pr p q L :
    p_proj (project_brn pr q L) p
    = pproj_brn pr q p [seq (X.1, p_proj X.2 p) | X <- L].
  Proof.
    case: pr=>[[f t] ty] /=.
    rewrite !(fun_if (fun X=> p_proj X p)).
    case: ifP =>// f_neq_t; case: ifP=>/=//[f_eq_g|f_neq_g].
    - rewrite pproj_sel; move: f_neq_t f_eq_g.
      by case: ifP=>[//|Eq1 Eq2 /eqP<-]; rewrite andbC eq_sym Eq2.
  Admitted.

  Lemma mdual_mrec Sp Sq : mdual (ms_rec Sp) (ms_rec Sq) = mdual Sp Sq.
  Proof. by case: Sp; case: Sq. Qed.

  Lemma mdual_msend_recv Sp Sq ty :
    mdual (ms_send ty Sp) (ms_recv ty Sq) = mdual Sp Sq.
  Proof. by case: Sp; case: Sq=>//Sp Sq/=; rewrite eq_refl. Qed.

  Lemma mdual_mrecv_send Sp Sq ty :
    mdual (ms_recv ty Sp) (ms_send ty Sq) = mdual Sp Sq.
  Proof. by case: Sp; case: Sq=>//Sp Sq/=; rewrite eq_refl. Qed.

  Lemma pproj_def mL p S :
    p_proj mL p == Some S ->
    exists L, (mL == Some L) && (partial_proj L p == Some S).
  Proof. by case: mL=>/=//L H; exists L; rewrite eq_refl H. Qed.

  Lemma mdual_msel_mbrn K K' :
    all2 (fun x y => mdual x.2 y.2) K K' ->
    mdual (ms_sel K) (ms_brn K').
  Proof.
    elim: K K'=>[|[l Sl] K Ih];case=>[|[r Sr] K']/=//.
    case: Sl; case: Sr=>/=//Sl Sr.
  Admitted.

  Lemma mdual_mbrn_msel K K' :
    all2 (fun x y => mdual x.2 y.2) K K' ->
    mdual (ms_brn K) (ms_sel K').
  Admitted.

  Lemma all2_map A B C (P : B -> C -> bool) f g (L : seq A) :
    all2 P [seq f x | x <- L] [seq g x | x <- L]
    = all (fun x => P (f x) (g x)) L.
  Proof. by elim: L => [|a L /=->]. Qed.

  Lemma dual_brn_sel K K1 :
    dual (s_brn K) (s_sel K1)
    = all2 (fun X Y => (X.1 == Y.1) && dual X.2 Y.2) K K1.
  Proof.
    elim: K K1=>// [[ll Ll] K Ih [|[lr Lr] K1]//].
    by move: Ih =>/=-Ih; rewrite Ih.
  Qed.

  Lemma dual_sel_brn K K1 :
    dual (s_sel K) (s_brn K1)
    = all2 (fun X Y => (X.1 == Y.1) && dual X.2 Y.2) K K1.
  Proof.
    elim: K K1=>// [[ll Ll] K Ih [|[lr Lr] K1]//]/=.
    by move: Ih =>/=-Ih; rewrite Ih.
  Qed.

  Lemma dual_eq A B C:
    dual A B ->
    dual A C ->
    B = C.
  Proof.
    elim/sty_ind: A B C=>[|v|L Ih|t L Ih|t L Ih|K Ih|K Ih] B C;case: B;case: C=>//.
    + move=> v0 v1; case: v; case: v0; case: v1=>//.
      - by move=> v v0 v1/==>/eqP->/eqP->.
      - by move=> v v0 v1/==>/eqP->/eqP->.
    + by move=> S S0 /= P1 P2; rewrite (Ih _ _ P1 P2).
    + move=> t0 L0 t1 L2 /= /andP-[/eqP-> P1] /andP-[/eqP-> P2].
      by rewrite (Ih _ _ P1 P2).
    + move=> t0 L0 t1 L2 /= /andP-[/eqP-> P1] /andP-[/eqP-> P2].
      by rewrite (Ih _ _ P1 P2).
    + move=> K0 K1; rewrite !dual_brn_sel.
      elim: K K0 K1 Ih=>//.
      * by move=> K0 K1 /=; case: K0; case: K1.
      * move=>[l1 S1] K1 Ih1 K2 K3 /= [Ih21 Ih22].
        case:K3;case:K2=>//[[l2 S2] K4 [l3 S3] K5 /=].
        move=>/andP-[/andP-[/eqP<- D13 K15]] /andP-[/andP-[/eqP<- D12 K14]].
        rewrite (Ih21 _ _ D13 D12).
        by move: Ih1=>/(_ K4 K5 Ih22 K15 K14)-[->].
    + move=> K0 K1; rewrite !dual_sel_brn.
      elim: K K0 K1 Ih=>//.
      * by move=> K0 K1 /=; case: K0; case: K1.
      * move=>[l1 S1] K1 Ih1 K2 K3 /= [Ih21 Ih22].
        case:K3;case:K2=>//[[l2 S2] K4 [l3 S3] K5 /=].
        move=>/andP-[/andP-[/eqP<- D13 K15]] /andP-[/andP-[/eqP<- D12 K14]].
        rewrite (Ih21 _ _ D13 D12).
        by move: Ih1=>/(_ K4 K5 Ih22 K15 K14)-[->].
  Qed.

  Lemma dual_sym A B:
    dual A B =
    dual B A.
  Proof.
    elim/sty_ind: A B=>//[|v|L Ih|t L Ih|t L Ih|K Ih|K Ih] B;case: B=>//.
    + by move=>v0/=; rewrite eq_sym.
    + by move=> ty L'/=; rewrite eq_sym Ih.
    + by move=> ty L'/=; rewrite eq_sym Ih.
    + elim: K Ih=>[|[l L] K /= Ih1 [Ih21 H22]].
      - move=> _; case=>//.
      - case=>// [[l' L'] K'] /=.
        by rewrite eq_sym Ih21 Ih1.
    + elim: K Ih=>[|[l L] K /= Ih1 [Ih21 H22]].
      - move=> _; case=>//.
      - case=>// [[l' L'] K'] /=.
        by rewrite eq_sym Ih21 Ih1.
  Qed.

  Lemma mdual_mergeall K K' :
    all2 (fun X Y => mdual X.2 Y.2) K K'
    -> mdual (merge_all K) (merge_all K').
  Proof.
    case: K K'=>[|[ll Ll]/= K]; case=>[|[ll' Ll']/= K']//.
    case: Ll; case: Ll'=>// Sl Sl'/=.
    move=>/andP-[] {ll ll'}.
    elim: K K' Sl Sl'=>[[|h K'] Sl Sl'//|[ll Ll] K Ih [//|[lr Lr] K'/=]].
    move=>Sl Sl' D /andP-[].
    case: Ll; case: Lr=>//Ll Lr/=.
    rewrite -[Some Lr == Some Sl']/(Lr == Sl') -[Some Ll == Some Sl]/(Ll == Sl).
    move: D; case: ifP=>[/eqP-> D1 D2|].
    - by rewrite (dual_eq D1 D2) eq_refl; apply: Ih.
    - case: ifP=>[/eqP->|]//.
      rewrite dual_sym [dual Lr _]dual_sym => Neq D1 D2.
      by move: (dual_eq D1 D2) =>/eqP; rewrite eq_sym Neq.
  Qed.

  Lemma all_compat G p q :
    p != q ->
    mdual (p_proj (project G p) q) (p_proj (project G q) p).
  Proof.
    move=> p_neq_q; elim/gty_ind2: G=>[|v/=|||]//.
    + move=> G/=.
      case: ifP=>[/eqP->/=//|].
      - case: (project G q)=>[Lq|]///=.
        rewrite !(fun_if (fun X => p_proj X p))/=.
        case: (partial_proj Lq p) =>//. do ! (case=>/=//).
        by do ! (case:ifP=>//).
      - case: ifP=>[/eqP->/=//|].
        * case: (project G p) =>/=// Lp.
          rewrite (fun_if (fun X => p_proj X q))/=.
          case: ifP=>//; case: (partial_proj Lp q)=>/=// Sp.
          rewrite (fun_if (fun X => mdual X None))/=.
          by case: Sp=>//; case=>//; case.
        * rewrite !pproj_rec.
          move=>_ _.
          move: (p_proj (project G p) q) (p_proj (project G q) p)=> Sp Sq.
          case: ifP=>[/eqP->|]; first (by move: Sq; do ! (case=>//)).
          case: ifP=>[/eqP->|]; first (by move: Sp; do ! (case=>//)).
          by rewrite mdual_mrec.
    + move=> pr G/=; rewrite !pproj_msg_swap.
      move: (p_proj (project G p) q) (p_proj (project G q) p) => Sp Sq Ih.
      case: pr=> [[f t] ty]/=; rewrite andbC; case: ifP=>//f_neq_t.
      case: ifP=>[/andP-[/eqP-> /eqP->]|];[rewrite (negPf p_neq_q)/=|].
      - by rewrite mdual_msend_recv.
      - move=>H; rewrite andbC; case: ifP=>//.
        by rewrite mdual_mrecv_send.
    + move=> pr G Ih/=; rewrite !pproj_brn_swap.
      rewrite -!map_comp /comp/=.
      case: pr=>[[f t] ty]/=.
      case: ifP=>//f_neq_t.
      rewrite andbC; case: ifP=>[/andP-[/eqP->/eqP->]|]//.
      - rewrite (negPf p_neq_q) /= mdual_msel_mbrn // all2_map/=.
        apply/forallP; last (by apply: Ih); move=>/=x; apply: idP.
      - move=>H; rewrite andbC; case: ifP=>[_|].
        * rewrite mdual_mbrn_msel // all2_map/=.
          apply/forallP; last (by apply: Ih); move=>/=x; apply: idP.
        * rewrite mdual_mergeall //. rewrite all2_map /=.
          apply/forallP; last (by apply: Ih); move=>/=x; apply: idP.
  Qed.

  Print Assumptions all_compat.
