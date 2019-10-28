From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.MP.Atom.
Require Import MPST.MP.Role.
Require Import MPST.MP.Forall.
Require Import MPST.MP.LNVar.
Require Import MPST.MP.Global.
Require Import MPST.MP.Local.
Require Import MPST.MP.Actions.

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
    | Some L => Some (l_rec L)
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

  Definition insert (E : role * l_ty) P :=
    match lookup E.1 P with
    | Some _ => P
    | None => E :: P
    end.

  Fixpoint project_all (g : g_ty) (r : seq role) : option (seq (role * l_ty)) :=
    match r with
    | [::] => Some [::]
    | h :: t => match project g h, project_all g t with
                | Some L, Some E => Some (insert (h, L) E)
                | _, _ => None
                end
    end.

  Fixpoint isg_valid d G :=
    match d with
    | 0 => match G with
           | g_var _ => false
           | _ => true
           end
    | S d =>
      match G with
      | g_rec G =>
        if G == g_end then false
        else isg_valid d (g_open 0 g_end G)
      | _ => true
      end
    end.

  Definition g_valid G := isg_valid (depth_gty G) G.

  Definition projection (g : g_ty) : option (seq (role * l_ty)) :=
    if g_valid g then project_all g (participants g)
    else None.

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
    | Some L, Some L' => is_dual L L'
    | None, None => true
    | _, _ => false
    end.

  Lemma mdualC l r : mdual l r = mdual r l.
  Proof. by case: l; case: r=>/=//l r; rewrite isdualC. Qed.

  Notation sbv n := (s_var (Rvar.bv n)).

  Lemma pproj_rec L p:
    p_proj (ml_rec L) p = if p_proj L p == Some (sbv 0)
                          then Some s_end
                          else ms_rec (p_proj L p).
  Proof. by case: L=>//L/=. Qed.

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
             (r1 r2 : role) (S : option s_ty) (K : seq (lbl * option s_ty)) :=
    let: ((p, q), t) := p in
    if p == q
    then None
    else if p == r1
         then if q == r2 then ms_sel K
              else merge_all K
         else if p == r2
              then if q == r1 then ms_brn K
                   else merge_all K
              else S.

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

  Lemma pproj_lbrn f L t:
    p_proj (ml_brn f L) t =
    if f == t then ms_brn [seq (X.1, p_proj X.2 t) | X <- L]
    else merge_all [seq (X.1, p_proj X.2 t) | X <- L].
  Proof.
    rewrite /ml_brn (fun_option (fun X => p_proj X t))/=.
    move: {-1} (flat_alts L) (eq_refl (flat_alts L)) => LL.
    case: LL=>[LL|]; first by move=>/flatalts_some->; rewrite -map_comp /comp/=.
    case:ifP=> _//; rewrite /ms_brn.
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

  Definition is_def A (L : option A)
    := match L with | Some _ => true | None => false end.

  Lemma pproj_mergeall L t:
    is_def (merge_all L) ->
    p_proj (merge_all L) t =
    merge_all [seq (X.1, p_proj X.2 t) | X <- L].
  Proof.
    case: L=>[|[l [L|]] K]/=//.
    elim: K=>/=; first (by rewrite eta_option).
    move=> [l' [L'|]] K Ih/=; last (by case: (partial_proj L t)).
    case: ifP=>[/eqP-[->{L'}] /Ih->{Ih}|//].
    by case: (partial_proj L t)=>// L'; rewrite eq_refl.
  Qed.

  Lemma mdual_mrec Sp Sq : mdual (ms_rec Sp) (ms_rec Sq) = mdual Sp Sq.
  Proof. by case: Sp; case: Sq. Qed.

  Lemma mdual_msend_recv Sp Sq ty :
    mdual (ms_send ty Sp) (ms_recv ty Sq) = mdual Sp Sq.
  Proof.
    case: Sp; case: Sq=>//Sp Sq/=; rewrite /is_dual/=.
    rewrite -[s_send _ _ == s_send _ _]/((ty == ty) && (Sq == dual Sp)).
    by rewrite eq_refl.
  Qed.

  Lemma mdual_mrecv_send Sp Sq ty :
    mdual (ms_recv ty Sp) (ms_send ty Sq) = mdual Sp Sq.
  Proof. by rewrite mdualC mdual_msend_recv mdualC. Qed.

  Lemma pproj_def mL p S :
    p_proj mL p == Some S ->
    exists L, (mL == Some L) && (partial_proj L p == Some S).
  Proof. by case: mL=>/=//L H; exists L; rewrite eq_refl H. Qed.

  Lemma mdual_msel_mbrn K K' :
    all2 (fun x y => (x.1 == y.1) && mdual x.2 y.2) K K' ->
    mdual (ms_sel K) (ms_brn K').
  Proof.
    rewrite /ms_sel /ms_brn; case: K; case: K'=>// lS K lS' K'.
    rewrite !flatalts_cons; move: {lS K lS' K'} (lS :: K) (lS' :: K')=> K K'.
    elim: K K'=>[|[l Sl] K Ih];case=>[|[r Sr] K']/=//.
    case: Sl; case: Sr=>///=; try (by rewrite -andbA andbC).
    move=> Sl Sr /andP-[/andP-[/eqP<- SlSr] /Ih-{Ih}].
    rewrite !option_comm /=.
    case: (flatten K'); case: (flatten K)=>//{K K'} K K'; rewrite /=/is_dual/=.
    by move: SlSr; rewrite/is_dual/==>/eqP<-; move=>/eqP-[<-].
  Qed.

  Lemma mdual_mbrn_msel K K' :
    all2 (fun x y => (x.1 == y.1) && mdual x.2 y.2) K K' ->
    mdual (ms_brn K) (ms_sel K').
  Proof.
    move=> H; suff: all2 (fun x y => (x.1 == y.1) && mdual x.2 y.2) K' K
             by move=>/mdual_msel_mbrn; rewrite mdualC.
    elim: K' K H=>[|h t Ih]; case=>[|h' t']/=//; move=>/andP-[/andP-[/eqP<-]].
    by rewrite mdualC=>-> /Ih->; rewrite eq_refl.
  Qed.

  Lemma all2_map A B C (P : B -> C -> bool) f g (L : seq A) :
    all2 P [seq f x | x <- L] [seq g x | x <- L]
    = all (fun x => P (f x) (g x)) L.
  Proof. by elim: L => [|a L /=->]. Qed.

  Lemma dual_brn_sel K K1 :
    is_dual (s_brn K) (s_sel K1)
    = all2 (fun X Y => (X.1 == Y.1) && is_dual X.2 Y.2) K K1.
  Proof.
    rewrite /is_dual; elim: K K1;[case=>//|].
    by move=>[ll Ll] K Ih [|[lr Lr] K1]/=//; move: Ih=>/(_ K1)<-.
  Qed.

  Lemma dual_sel_brn K K1 :
    is_dual (s_sel K) (s_brn K1)
    = all2 (fun X Y => (X.1 == Y.1) && is_dual X.2 Y.2) K K1.
  Proof.
    rewrite /is_dual; elim: K K1;[case=>//|].
    by move=>[ll Ll] K Ih [|[lr Lr] K1]/=//; move: Ih=>/(_ K1)<-.
  Qed.

  Lemma dual_eq A B C:
    is_dual A B ->
    is_dual A C ->
    B = C.
  Proof.
    rewrite /is_dual =>/eqP/(f_equal dual).
    rewrite dualK=><- /eqP/(f_equal dual)->.
    by rewrite dualK.
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
      rewrite isdualC [is_dual Lr _]isdualC => Neq D1 D2.
      by move: (dual_eq D1 D2) =>/eqP; rewrite eq_sym Neq.
  Qed.

  Definition WFp (p : role) G := is_def (project G p).

  Definition WFps (ps : seq role) G :=
    forall p, p \in ps -> is_def (project G p).

  Lemma wf_rec p G :
    WFp p (g_rec G) ->
    (project G p != Some (lbv 0)) /\ WFp p G.
  Proof. by rewrite /WFp/=; case: ifP=>///=; case: (project G p). Qed.

  Lemma wf_msg p pr G :
    WFp p (g_msg pr G) -> (pr.1.1 != pr.1.2) && WFp p G.
  Proof.
    case: pr=>[[f t] ty]; rewrite /WFp/=; case: ifP=>///=.
    by do ! (case: ifP=>//); case: (project G p).
  Qed.

  Lemma isdef_sel q K :
    is_def (ml_sel q K) -> all (fun X => is_def X.2) K.
  Proof.
    rewrite /ml_sel; case: K=>// lL K; rewrite flatalts_cons.
    move: {lL K}(lL :: K)=>K.
    elim:K=>[//|[l [L|//]] K Ih]/=.
    by rewrite option_comm=> H; apply: Ih; move: H; case: (flatten K).
  Qed.

  Lemma isdef_merge (A : eqType) (K : seq (lbl * option A)) :
    is_def (merge_all K) -> all (fun X => is_def X.2) K.
  Proof.
    rewrite /merge_all; case: K=>[//|[l [o|//]]  K]/={l}.
    by elim:K=>[//|[l [L|//]] K Ih]/=; case:ifP.
  Qed.

  Lemma isdef_brn q K :
    is_def (ml_brn q K) -> all (fun X => is_def X.2) K.
  Proof.
    rewrite /ml_brn ; case: K=>// lL K; rewrite flatalts_cons.
    move: {lL K}(lL :: K)=>K.
    elim:K=>[//|[l [L|//]] K Ih]/=.
    by rewrite option_comm=> H; apply: Ih; move: H; case: (flatten K).
  Qed.

  Lemma all_compat G p q :
    p != q ->
    WFp p G ->
    WFp q G ->
    mdual (p_proj (project G p) q) (p_proj (project G q) p).
  Proof.
    move=>p_neq_q; elim/gty_ind1:G=>[|v/=|G|pr G|[[f t] ty] G]///=.
    + by rewrite is_dual_var.
    + rewrite (fun_if (p_proj^~p)) (fun_if (p_proj^~q)) !pproj_rec /=.
      move=> Ih /wf_rec-[/negPf--> Wfp2] /wf_rec-[/negPf--> Wfq2].
      move: (p_proj (project G p) q) (p_proj (project G q) p) (Ih Wfp2 Wfq2).
      move=>S1 S2 {Ih Wfp2 Wfq2 p_neq_q p q G}.
      do 2 (case: S1; case: S2=>// S1 S2/=).
      by move=>/eqP-[->]; case: ifP=>///=; rewrite /is_dual/dual.
    + rewrite !pproj_msg_swap.
      move: (p_proj (project G p) q) (p_proj (project G q) p) => Sp Sq Ih.
      case: pr=> [[f t] ty]/=; rewrite andbC; case: ifP=>//f_neq_t.
      move=> /wf_msg-/andP-[_ Wf1] /wf_msg-/andP-[_ Wf2].
      case: ifP=>[/andP-[/eqP-> /eqP->]|];[rewrite (negPf p_neq_q)/=|].
      - by rewrite mdual_msend_recv; apply: Ih.
      - move=>H; rewrite andbC; case: ifP=>[_|_]; last (by apply: Ih).
        by rewrite mdual_mrecv_send; apply: Ih.
    + rewrite !(fun_if(fun X=> p_proj X p)) !(fun_if(fun X=> p_proj X q))/=.
      rewrite !pproj_sel !pproj_lbrn -!map_comp /comp/=.
      rewrite /WFp/=; do ! (case: ifP=>//).
      - by move=>/eqP->; rewrite (negPf p_neq_q).
      - by move=>_ _ /eqP->; rewrite eq_sym (negPf p_neq_q).
      - by move=> _ _ /eqP->; rewrite eq_sym (negPf p_neq_q).
      - by move=> _ _ /eqP->; rewrite eq_sym (negPf p_neq_q).
      - move=>/eqP-> _ /eqP-> _/= Ih /isdef_sel.
        rewrite all_map /pred_of_simpl/preim/SimplPred/fun_of_simpl/=.
        move=>/forallbP/forall_member-H1 /isdef_brn.
        rewrite all_map /pred_of_simpl/preim/SimplPred/fun_of_simpl/=.
        move=>/forallbP/forall_member-H2; rewrite mdual_msel_mbrn // all2_map/=.
        apply/forallbP/forall_member =>x xG; rewrite eq_refl/=.
        move: Ih H1 H2 =>/(_ x xG)-Ih /(_ x xG)-H1 /(_ x xG)-H2.
        by apply: Ih.
      - move=> _ _/eqP-> _ Ih.
        move=>/isdef_sel/forallbP/Fa_map/=/forall_member-H1 H2.
        rewrite pproj_mergeall // -map_comp /comp/=; apply: mdual_mergeall.
        move: H2 =>/isdef_merge/forallbP/Fa_map//=/forall_member-H2.
        rewrite all2_map; apply/forallbP/forall_member=> /=- x xG.
        by move: H1 H2 Ih=>/(_ x xG)-H1 /(_ x xG)-H2 /(_ x xG H1 H2).
      - move=>/eqP-> /eqP-> _ _ Ih /isdef_brn.
        rewrite all_map/pred_of_simpl/preim/SimplPred/fun_of_simpl/=.
        move=>/forallbP/forall_member=> H1 /isdef_sel.
        rewrite all_map/pred_of_simpl/preim/SimplPred/fun_of_simpl/=.
        move=>/forallbP/forall_member=> H2.
        apply/mdual_mbrn_msel; rewrite all2_map/=.
        apply/forallbP/forall_member=> x xG; rewrite eq_refl.
        by move: H1 H2 Ih=> /(_ x xG)-H1 /(_ x xG)-H2 /(_ x xG H1 H2).
      - by move=>/eqP-> _; rewrite eq_sym (negPf p_neq_q).
      - move=> _ _ /eqP-> _ _ Ih.
        move=>/isdef_brn/forallbP/Fa_map/=/forall_member-H1 H2.
        rewrite pproj_mergeall // -map_comp /comp/=; apply: mdual_mergeall.
        move: H2 =>/isdef_merge/forallbP/Fa_map//=/forall_member-H2.
        rewrite all2_map; apply/forallbP/forall_member=> /=- x xG.
        by move: H1 H2 Ih=>/(_ x xG)-H1 /(_ x xG)-H2 /(_ x xG H1 H2).
      - move=> /eqP-> _ _ _ Ih H1.
        rewrite pproj_mergeall // -map_comp /comp/=; move: H1.
        move=>/isdef_merge/forallbP/Fa_map/=/forall_member-H1.
        move=>/isdef_sel/forallbP/Fa_map/=/forall_member-H2.
        apply: mdual_mergeall; rewrite all2_map.
        apply/forallbP/forall_member=> /=- x xG.
        by move: H1 H2 Ih=>/(_ x xG)-H1 /(_ x xG)-H2 /(_ x xG H1 H2).
      - move=> /eqP-> _ _ _ _ Ih H1.
        rewrite pproj_mergeall // -map_comp /comp/=; move: H1.
        move=>/isdef_merge/forallbP/Fa_map/=/forall_member-H1.
        move=>/isdef_brn/forallbP/Fa_map/=/forall_member-H2.
        apply: mdual_mergeall; rewrite all2_map.
        apply/forallbP/forall_member=> /=- x xG.
        by move: H1 H2 Ih=>/(_ x xG)-H1 /(_ x xG)-H2 /(_ x xG H1 H2).
      - move=> _ _ _ _ _ Ih H1 H2.
        rewrite !pproj_mergeall // -!map_comp /comp/=; move: H1 H2.
        move=>/isdef_merge/forallbP/Fa_map/=/forall_member-H1.
        move=>/isdef_merge/forallbP/Fa_map/=/forall_member-H2.
        apply: mdual_mergeall; rewrite all2_map.
        apply/forallbP/forall_member=> /=- x xG.
        by move: H1 H2 Ih=>/(_ x xG)-H1 /(_ x xG)-H2 /(_ x xG H1 H2).
  Qed.

End Project.
