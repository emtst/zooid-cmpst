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
Require Import MPST.Actions.

Section Project.

  Definition ml_act (a : l_act) (r : role) (Ks : seq (lbl * (mty * option l_ty))) :=
    match flat_alts Ks with
    | Some x => Some (l_msg a r x)
    | None => None
    end.

  Open Scope mpst_scope.
  Definition project_brn (p : role) (q : role) (r : role)
             (K : seq (lbl * (mty * option l_ty))) :=
    if p == q
    then None
    else if p == r
         then ml_act l_send q K
         else if q == r
              then ml_act l_recv p K
              else merge_all [seq x.cnt | x <- K].

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

  Notation g_ty := (g_ty unit).

  Fixpoint project (g : g_ty) (r : role) : option l_ty :=
    match g with
    | g_end => Some l_end
    | g_var v => Some (l_var v)
    | g_rec G => let L := project G r in
                 if L == Some (lbv 0) then None else ml_rec L
    | g_msg _ p q K =>
      project_brn p q r [seq (X.lbl, (X.mty, project X.cnt r)) | X <- K]
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

  Fixpoint isg_valid (d : nat) (G : g_ty) := true.
  (*
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
   *)

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

  Definition pproj_brn (p : g_prefix)
             (r1 r2 : role) (S : option s_ty)
             (K : seq (lbl * (mty * option s_ty))) :=
    let: ((p, q), t) := p in
    if p == q
    then None
    else if p == r1
         then if q == r2 then ms_msg l_send K
              else merge_all [seq X.cnt | X <- K ]
         else if p == r2
              then if q == r1 then ms_msg l_recv K
                   else merge_all [seq X.cnt | X <- K ]
              else S.

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


  Lemma flatten_some (A : eqType) (L : seq (lbl * (mty * option A))) LL :
    flatten L == Some LL ->
    L = [seq (X.lbl, (X.mty, Some X.cnt)) | X <- LL].
  Proof.
    elim: L LL=>[LL /eqP-[<-]//| [l [t L]] K Ih K']/=.
    case: L=>//a; move: Ih; case: (flatten K)=>//FK Ih /eqP-[<-]/=.
    by rewrite -Ih.
  Qed.

  Lemma flatalts_some (A : eqType) (L : seq (lbl * (mty * option A))) LL :
    flat_alts L == Some LL ->
    L = [seq (X.lbl, (X.mty,  Some X.cnt)) | X <- LL].
  Proof. by case: L=>// L K; apply: flatten_some. Qed.

  Lemma flatten_none (A : eqType) (L : seq (lbl * (mty * option A))) :
    flatten L == None -> exists l t, (l, (t, None)) \in L.
  Proof.
    elim: L=>[// | [l [t [S|]]] K]/=; move=> Ih F_none.
    + have {F_none} /Ih: flatten K == None by case: (flatten K) F_none.
      by move=>[l0 [t0 Pf]]; exists l0; exists t0; rewrite in_cons orbC Pf.
    + by exists l; exists t; rewrite in_cons eq_refl.
  Qed.

  Lemma flatalts_none (A : eqType) (L : seq (lbl * (mty * option A))) :
    flat_alts L == None -> L == [::] \/ exists l t, (l, (t, None)) \in L.
  Proof.
    case: L; first by move=> _; left.
    by move=> a L H; right; apply: flatten_none.
  Qed.

  Lemma flatten_pproj (L : seq (lbl * (mty * option l_ty))) t :
    flatten [seq (X.lbl, (X.mty, p_proj X.cnt t)) | X <- L]
    = match flatten L with
      | Some K => flatten [seq (X.lbl, (X.mty, partial_proj X.cnt t)) | X <- K]
      | None => None
      end.
  Proof.
    elim: L=>// [[l [ty [S|]]] K]///=.
    move=>->/=; rewrite option_comm/=.
    case: (partial_proj S t)=>[FK|]; last (by case: (flatten K)).
    by rewrite option_comm.
  Qed.

  Lemma flatalts_cons (A : eqType) (a : lbl * (mty * option A)) L :
    flat_alts (a :: L) = flatten (a :: L).
  Proof. by []. Qed.

  Lemma flatalts_pproj L  t :
    flat_alts [seq (X.lbl, (X.mty, p_proj X.cnt t)) | X <- L]
    = match flat_alts L with
      | Some K => flat_alts [seq (X.lbl, (X.mty, partial_proj X.cnt t)) | X <- K]
      | None => None
      end.
  Proof.
    case: L=>// a L; rewrite map_cons !flatalts_cons -map_cons flatten_pproj.
    case: {-1} (flatten (a::L)) (eq_refl (flatten (a::L)))=>// K.
    by move=>/flatten_some; case: K.
  Qed.

  Lemma pproj_msg a f L t:
    p_proj (ml_act a f L) t =
    if f == t then ms_msg a [seq (X.lbl, (X.mty, p_proj X.cnt t)) | X <- L]
    else merge_all [seq p_proj X.cnt t | X <- L].
  Proof.
    rewrite /ml_act (fun_option (fun X => p_proj X t))/=.
    move: {-1} (flat_alts L) (eq_refl (flat_alts L)) => LL.
    case: LL=>[LL|]; first (by move=>/flatalts_some->; rewrite -!map_comp /comp/=).
    case:ifP=> _//; rewrite /ms_msg.
    - by rewrite flatalts_pproj=>/eqP->.
    - move=>/flatalts_none-[/eqP->//|[l [t0]]].
      rewrite /merge_all; case: L=>// a' K/=.
      case: a'=>[l' [t' [S|]]]//.
      rewrite in_cons !xpair_eqE andbA andbC/=.
      case: (partial_proj S t)=>// {S}S.
      elim: K=>// [[l'' [t'' [S'|]]] K]// Ih.
      rewrite in_cons !xpair_eqE andbA andbC/==>/Ih-{Ih}Ih.
      by case: (partial_proj S' t)=>// {S'}S'; case:ifP=>//.
  Qed.

  Definition is_def A (L : option A)
    := match L with | Some _ => true | None => false end.

  Lemma pproj_mergeall L t:
    is_def (merge_all L) ->
    p_proj (merge_all L) t =
    merge_all [seq p_proj X t | X <- L].
  Proof.
    case: L=>[|[L|] K]/=//.
    elim: K=>/=; first (by rewrite eta_option).
    move=> [L'|] K Ih/=; last (by case: (partial_proj L t)).
    case: ifP=>[/eqP-[->{L'}] /Ih->{Ih}|//].
    by case: (partial_proj L t)=>// L'; rewrite eq_refl.
  Qed.

  Lemma mdual_mrec Sp Sq : mdual (ms_rec Sp) (ms_rec Sq) = mdual Sp Sq.
  Proof. by case: Sp; case: Sq. Qed.

  Lemma pproj_def mL p S :
    p_proj mL p == Some S ->
    exists L, (mL == Some L) && (partial_proj L p == Some S).
  Proof. by case: mL=>/=//L H; exists L; rewrite eq_refl H. Qed.

  Lemma mdual_act a a' K K' :
    dual_act a == a' ->
    all2 (fun x y => (x.lbl == y.lbl) && (x.mty == y.mty) && mdual x.cnt y.cnt) K K' ->
    mdual (ms_msg a K) (ms_msg a' K').
  Proof.
    move=>/eqP<-{a'}; rewrite /ms_msg; case: K; case: K'=>// lS K lS' K'.
    rewrite !flatalts_cons; move: {lS K lS' K'} (lS :: K) (lS' :: K')=> K K'.
    elim: K K'=>[|[l [tl Sl]] K Ih];case=>[|[r [tr Sr]] K']/=//.
    - by rewrite /is_dual/dual//= dual_actK.
    - case: Sl; case: Sr=>///=; try (by rewrite -andbA andbC).
      move=> Sl Sr /andP-[/andP-[/andP-[/eqP<-/eqP<- SlSr]]] /Ih-{Ih}.
      rewrite !option_comm /=.
      case: (flatten K'); case: (flatten K)=>//{K K'} K K'; rewrite /=/is_dual/=.
      by move: SlSr; rewrite /is_dual/==>/eqP<-; move=>/eqP-[<-<-].
  Qed.

  Lemma all2_map A B C (P : B -> C -> bool) f g (L : seq A) :
    all2 P [seq f x | x <- L] [seq g x | x <- L]
    = all (fun x => P (f x) (g x)) L.
  Proof. by elim: L => [|a L /=->]. Qed.

  Lemma dual_msg a a' K K1 :
    is_dual (s_msg a K) (s_msg a' K1)
    = (a == dual_act a')
        && all2 (fun X Y => (X.lbl == Y.lbl) && (X.mty == Y.mty) && is_dual X.cnt Y.cnt) K K1.
  Proof.
    case:eqP=>[->{a}|/eqP]; rewrite/is_dual/=; last (by apply: contraNF =>/eqP[->]).
    - move: (dual_act a') => {a'}a; rewrite !eqE /= eq_refl /= -!/eqE.
      by elim: K K1=>[|L K Ih]; case=>// [L1 K1]/=; rewrite Ih.
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
    all2 (fun X Y => mdual X Y) K K'
    -> mdual (merge_all K) (merge_all K').
  Proof.
    case: K K'=>[|Ll/= K]; case=>[|Ll'/= K']//.
    case: Ll; case: Ll'=>// Sl Sl'/=.
    move=>/andP-[].
    elim: K K' Sl Sl'=>[[|h K'] Sl Sl'//|Ll K Ih [//|Lr K'/=]].
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

  Lemma isdef_sel a q K :
    is_def (ml_act a q K) -> all (fun X => is_def X.cnt) K.
  Proof.
    rewrite /ml_act; case: K=>// lL K; rewrite flatalts_cons.
    move: {lL K}(lL :: K)=>K.
    elim:K=>[//|[l [t [L|//]]] K Ih]/=.
    by rewrite option_comm=> H; apply: Ih; move: H; case: (flatten K).
  Qed.

  Lemma isdef_merge (A : eqType) (K : seq (option A)) :
    is_def (merge_all K) -> all (fun X => is_def X) K.
  Proof.
    rewrite /merge_all; case: K=>[//|[o|//]  K]/=.
    by elim:K=>[//|[L|//] K Ih]/=; case:ifP.
  Qed.

  Lemma all_compat G p q :
    p != q ->
    WFp p G ->
    WFp q G ->
    mdual (p_proj (project G p) q) (p_proj (project G q) p).
  Proof.
    move=>p_neq_q; elim/gty_ind1:G=>[|v/=|G|m f t G]///=.
    + by rewrite is_dual_var.
    + rewrite (fun_if (p_proj^~p)) (fun_if (p_proj^~q)) !pproj_rec /=.
      move=> Ih /wf_rec-[/negPf--> Wfp2] /wf_rec-[/negPf--> Wfq2].
      move: (p_proj (project G p) q) (p_proj (project G q) p) (Ih Wfp2 Wfq2).
      move=>S1 S2 {Ih Wfp2 Wfq2 p_neq_q p q G}.
      do 2 (case: S1; case: S2=>// S1 S2/=).
      by move=>/eqP-[->]; case: ifP=>///=; rewrite /is_dual/dual.
    + rewrite !(fun_if(fun X=> p_proj X p)) !(fun_if(fun X=> p_proj X q))/=.
      rewrite !pproj_msg -!map_comp /comp/=.
      rewrite /WFp/=/project_brn.
      do ! (case: ifP=>[H|_];[rewrite ?(eqP H) ?(negPf p_neq_q)//; move: H|]).
      - move => _  _/= Ih /isdef_sel.
        rewrite all_map /pred_of_simpl/preim/SimplPred/fun_of_simpl/=.
        move=>/forallbP/forall_member-H1 /isdef_sel.
        rewrite all_map /pred_of_simpl/preim/SimplPred/fun_of_simpl/=.
        move=>/forallbP/forall_member-H2; rewrite mdual_act // all2_map/=.
        apply/forallbP/forall_member =>x xG; rewrite eq_refl/=.
        move: Ih H1 H2 =>/(_ x xG)-Ih /(_ x xG)-H1 /(_ x xG)-H2.
        by rewrite eq_refl /=; apply: Ih.
      - move=> _ Ih.
        move=>/isdef_sel/forallbP/Fa_map/=/forall_member-H1.
        rewrite -map_comp/comp/==>H2.
        rewrite pproj_mergeall // -map_comp /comp/=; apply: mdual_mergeall.
        move: H2 =>/isdef_merge/forallbP/Fa_map//=/forall_member-H2.
        rewrite all2_map; apply/forallbP/forall_member=> /=- x xG.
        by move: H1 H2 Ih=>/(_ x xG)-H1 /(_ x xG)-H2 /(_ x xG H1 H2).
      - move=> _ _ Ih /isdef_sel.
        rewrite all_map/pred_of_simpl/preim/SimplPred/fun_of_simpl/=.
        move=>/forallbP/forall_member=> H1 /isdef_sel.
        rewrite all_map/pred_of_simpl/preim/SimplPred/fun_of_simpl/=.
        move=>/forallbP/forall_member=> H2.
        apply/mdual_act=>//; rewrite all2_map/=.
        apply/forallbP/forall_member=> x xG; rewrite !eq_refl/=.
        by move: H1 H2 Ih=> /(_ x xG)-H1 /(_ x xG)-H2 /(_ x xG H1 H2).
      - move=> _ Ih.
        move=>/isdef_sel/forallbP/Fa_map/=/forall_member-H1.
        rewrite -map_comp/comp/==>H2.
        rewrite pproj_mergeall // -map_comp /comp/=; apply: mdual_mergeall.
        move: H2 =>/isdef_merge/forallbP/Fa_map//=/forall_member-H2.
        rewrite all2_map; apply/forallbP/forall_member=> /=- x xG.
        by move: H1 H2 Ih=>/(_ x xG)-H1 /(_ x xG)-H2 /(_ x xG H1 H2).
      - move=> _ Ih.
        rewrite -map_comp/comp/==>H1.
        rewrite pproj_mergeall // -map_comp /comp/=; move: H1.
        move=>/isdef_merge/forallbP/Fa_map/=/forall_member-H1.
        move=>/isdef_sel/forallbP/Fa_map/=/forall_member-H2.
        apply: mdual_mergeall; rewrite all2_map.
        apply/forallbP/forall_member=> /=- x xG.
        by move: H1 H2 Ih=>/(_ x xG)-H1 /(_ x xG)-H2 /(_ x xG H1 H2).
      - move=> _ Ih.
        rewrite -map_comp/comp/==>H1.
        rewrite pproj_mergeall // -map_comp /comp/=; move: H1.
        move=>/isdef_merge/forallbP/Fa_map/=/forall_member-H1.
        move=>/isdef_sel/forallbP/Fa_map/=/forall_member-H2.
        apply: mdual_mergeall; rewrite all2_map.
        apply/forallbP/forall_member=> /=- x xG.
        by move: H1 H2 Ih=>/(_ x xG)-H1 /(_ x xG)-H2 /(_ x xG H1 H2).
      - move=> Ih.
        rewrite -!map_comp/comp/==>H1 H2.
        rewrite !pproj_mergeall // -!map_comp /comp/=; move: H1 H2.
        move=>/isdef_merge/forallbP/Fa_map/=/forall_member-H1.
        move=>/isdef_merge/forallbP/Fa_map/=/forall_member-H2.
        apply: mdual_mergeall; rewrite all2_map.
        apply/forallbP/forall_member=> /=- x xG.
        by move: H1 H2 Ih=>/(_ x xG)-H1 /(_ x xG)-H2 /(_ x xG H1 H2).
  Qed.

End Project.
