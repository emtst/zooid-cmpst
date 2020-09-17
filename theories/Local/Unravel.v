From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco2.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.

Require Import MPST.Local.Syntax.
Require Import MPST.Local.Tree.

Definition lty_rel := rel2 l_ty (fun=>rl_ty).
Inductive l_unroll (r : lty_rel) : l_ty -> rl_ty -> Prop :=
| lu_end :
    @l_unroll r l_end rl_end
| lu_rec G G' :
    r (l_open 0 (l_rec G) G) G' ->
    @l_unroll r (l_rec G) G'
| lu_msg a p Ks C :
    same_dom (find_cont Ks) C ->
    R_all r (find_cont Ks) C ->
    @l_unroll r (l_msg a p Ks) (rl_msg a p C)
.
Hint Constructors l_unroll.

Scheme lunroll_ind := Induction for l_unroll Sort Prop.

Lemma l_unroll_monotone : monotone2 l_unroll.
Proof.
  move=>IL CL r r' U H; move: IL CL U.
  elim=>[|V|L IH|a F Ks IH] CL//=;
    case E:_ _/ =>[|G G' R|a' F' Ks' C D U]//.
  - by move: E R => [<-] /H; constructor.
  - by constructor=>// l Ty IL {}CL H0 /(U _ _ _ _ H0)/H.
Qed.
Hint Resolve l_unroll_monotone.

Definition LUnroll IL CL := paco2 l_unroll bot2 IL CL.

Definition lu_unfold := paco2_unfold l_unroll_monotone.

Lemma LUnroll_ind n iG cG :
  LUnroll iG cG <-> LUnroll (lunroll n iG) cG.
Proof.
  split.
  - elim: n =>[//|n Ih] in iG cG *; case: iG=>//= iL /lu_unfold.
    by case E: _ _/ => [|L L' [|]|]//; move: E=>[->]; apply/Ih.
  - elim: n =>// n Ih in iG cG *; case: iG=>//= G /Ih-H1.
    by apply/paco2_fold; constructor; left.
Qed.

Lemma lunroll_end cL :
  LUnroll l_end cL -> cL = rl_end.
Proof. by move=> /lu_unfold-LU; case Eq: _ _ / LU. Qed.

Lemma l_guarded_unroll iG :
  l_closed (l_rec iG) -> lguarded 0 (l_rec iG) ->
  lguarded 0 (l_open 0 (l_rec iG) iG).
Proof.
  move=> C GG; have GG': (lguarded 1 iG) by move:GG C=>/=; case: iG.
  by move: (lguarded_open 0 GG C GG')=>/lguarded_depth_gt/(_ (lopen_closed C)).
Qed.

Lemma l_guarded_nunroll n iL :
  l_closed iL -> lguarded 0 iL -> lguarded 0 (lunroll n iL).
Proof.
  elim: n iL=>[|n Ih]//;case=>// iG CG /(l_guarded_unroll CG)/Ih-H/=.
  by apply/H/lopen_closed.
Qed.

Lemma l_closed_unroll n iL :
  l_closed iL -> l_closed (lunroll n iL).
Proof. by elim: n iL=>[|n Ih]//=; case=>//= iG /lopen_closed/Ih. Qed.

Lemma v_lty G : (exists v, G = l_var v) \/ (forall v, G != l_var v).
Proof. by case: G; try (by right); move=>v;left;exists v. Qed.

Lemma lguarded_lbinds_lt s Lr :
  l_binds s Lr = false ->
  lguarded s Lr ->
  lguarded s.+1 Lr.
Proof.
  move: {-1}(lrec_depth Lr) (erefl (lrec_depth Lr))=> n E.
  elim: n=>[|n Ih] in s Lr E *.
  - by case: Lr E=>//= v _ /(rwP negPf); rewrite ltn_neqAle eq_sym=>->->.
  - case: Lr E=>//= L [/Ih-E]; apply/E.
Qed.

CoFixpoint l_expand (l : l_ty) : rl_ty :=
  match lunroll (lrec_depth l) l with
  | l_msg a T Ks =>
    rl_msg a T
           (fun l =>
              match find_cont Ks l with
              | Some (Ty, L) => Some (Ty, l_expand L)
              | None => None
              end)
  | _ => rl_end
  end.

Lemma rltyU G : G = match G with
                    | rl_msg a T C => rl_msg a T C
                    | rl_end => rl_end
                    end.
Proof. by case: G. Qed.

Fixpoint l_non_empty_cont G :=
  match G with
  | l_msg _ _ Ks => ~~ nilp Ks && all id [seq l_non_empty_cont K.2.2 | K <- Ks]
  | l_rec G => l_non_empty_cont G
  | _ => true
  end.

Definition l_precond L :=
  l_closed L && lguarded 0 L && l_non_empty_cont L.

Lemma lne_shift d n G :
  l_non_empty_cont G ->
  l_non_empty_cont (l_shift d n G).
Proof.
  elim: G=>[|v|L Ih|a p Ks Ih]//= in n *.
  - by case: ifP.
  - by apply/Ih.
  - move=>/andP-[NIL NE]; apply/andP;split;first by move: Ks NIL {Ih NE}=>[].
    rewrite -map_comp /comp/=; move: NE=>/forallbP/forall_member/member_map.
    move=>/(_ _ ((rwP (memberP _ _)).2 _))=> H.
    apply/forallbP/forall_member/member_map=>b /(rwP (memberP _ _))-IN.
    by apply: (Ih _ IN _ (H _ IN)).
Qed.

Lemma lne_open n G G' :
  l_non_empty_cont G -> l_non_empty_cont G' -> l_non_empty_cont (l_open n G' G).
Proof.
  move=> NE1 NE2; move: NE1.
  elim: G n=>//.
  - by move=> v n; rewrite /=; case: ifP=>// _ _; apply/lne_shift.
  - by move=> G Ih n /=; apply/Ih.
  - move=> a T C Ih n /=; case: C Ih=>//= K Ks Ih /andP-[NE_K ALL].
    have K_in: K \in K :: Ks by rewrite in_cons !eq_refl.
    rewrite (Ih K K_in n NE_K) /= {NE_K}.
    move: ALL=>/forallbP/forall_member/member_map-ALL.
    apply/forallbP/forall_member/member_map/member_map=>/=K' M.
    move: M (ALL _ M)=>/memberP-M {}ALL.
    have K'_in : K' \in K :: Ks by rewrite in_cons M orbT.
    by apply/(Ih _ K'_in n)/ALL.
Qed.

Lemma lne_unr n G : l_non_empty_cont G -> l_non_empty_cont (lunroll n G).
Proof.
  elim: n G=>[//|n/=] Ih; case=>//= G NE.
  have: l_non_empty_cont (l_rec G) by [].
  by move=>/(lne_open 0 NE); apply/Ih.
Qed.

Definition l_expand' L :=
  match L with
  | l_msg a T Ks =>
    rl_msg a T (fun l : lbl => match find_cont Ks l with
                               | Some (Ty, L0) => Some (Ty, l_expand L0)
                               | None => None
                               end)
  | _ => rl_end
  end.

Lemma l_expand_once L : l_expand L = l_expand' (lunroll (lrec_depth L) L).
Proof.
  by rewrite (rltyU (l_expand _)) /l_expand /l_expand'-rltyU-/l_expand.
Qed.

Lemma l_expand_unr L :
  lguarded 0 L ->
  l_closed L ->
  l_non_empty_cont L ->
  LUnroll L (l_expand L).
Proof.
  move=>gG cG NE; rewrite l_expand_once.
  move: {-1}(l_expand' _) (erefl (l_expand' (lunroll (lrec_depth L) L))).
  move=>CG ECG; move: L CG {ECG gG cG NE}(conj ECG (conj gG (conj cG NE))).
  apply/paco2_acc=>r _ /(_ _ _ (conj erefl (conj _ (conj _ _))))-CIH.
  move=> G CG [<-]{CG} [gG][cG][NE].
  case: G cG gG NE.
  - move=>_ _ _ /=; by apply/paco2_fold; constructor.
  - by move=>V /lclosed_not_var/(_ V)/eqP/(_ erefl).
  - move=>G cG gG nE /=;apply/paco2_fold.
    constructor; right; have gG': lguarded 1 G by move: gG.
    rewrite (lguarded_recdepth (m:=0) gG' _ (l_rec G)) //.
    apply/CIH.
    by apply/l_guarded_unroll.
    by apply/lopen_closed.
    by apply/lne_open.
  - move=>F T C cG gG NE; apply/paco2_fold; constructor.
    + move=>l Ty; case: find_cont=>[[Ty0 L0]|]//; split=>[][G]//[->] _.
      * by exists (l_expand L0).
      * by exists L0.
    + move=> l Ty G CG FND; rewrite FND=>[][<-]; right.
      move: cG; rewrite /l_closed/==>/flatten_eq_nil/member_map-cG.
      move: gG; rewrite /==>/forallbP/forall_member-gG.
      move: NE=>/==>/andP-[NE_C]/forallbP/forall_member/member_map-NE.
      move: (find_member FND)=>MEM.
      rewrite l_expand_once.
      by apply/(CIH _ (gG _ MEM) (cG _ MEM) (NE _ MEM)).
Qed.

Lemma LUnroll_EqL L CL CL' : LUnroll L CL -> EqL CL CL' -> LUnroll L CL'.
Proof.
  move=> H1 H2; move: L CL' {H1 H2 CL} (ex_intro (fun=>_) CL (conj H1 H2)).
  apply/paco2_acc=>r _ /(_ _ _ (ex_intro _ _ (conj _ _)))-CIH.
  move=> L CL [CL'][LU]EQ.
  move: LU EQ=>/(paco2_unfold l_unroll_monotone); case.
  - move=>/(paco2_unfold EqL_monotone); case E: _ _ / =>//.
    by apply/paco2_fold; constructor.
  - move=> G G' [/CIH-GU|//] /GU-H.
    by apply/paco2_fold; constructor; right.
  - move=> a p Ks C DOM ALL; move=>/(paco2_unfold EqL_monotone).
    case E: _ _ / =>[|a' p' CL1 CL2 DOM' EQ_ALL]//.
    move: E DOM' EQ_ALL=>[<-<-<-] DOM' E_ALL {a' p' CL1}.
    apply/paco2_fold; constructor; first by apply/(same_dom_trans DOM).
    move=>l Ty G iL Cl CCl; right.
    move: (dom DOM Cl)=>[LL]Cl'.
    move: (ALL _ _ _ _ Cl Cl')=>[UG|//].
    move: (E_ALL _ _ _ _ Cl' CCl)=>[EG|//].
    by apply/(CIH _ _ _ UG EG).
Qed.

Lemma lunroll_inf Li Lr Li' :
  lunroll (lrec_depth Li) Li = l_rec Li' ->
  LUnroll Li Lr.
Proof.
  rewrite lunroll_nopen=>/nopen_rec-[m]; rewrite add0n=>[][BND].
  rewrite {2}(nrec_lrecdepthI Li).
  move: (getnr_nonrec Li) BND; case: (get_nr Li)=>//= v _ /eqP->.
  move: (lrec_depth Li)=>d {v Li Li'}.
  move EQ: (n_rec d (l_var m))=>Li LT; move: {EQ LT}(conj EQ LT)=>H.
  move: (ex_intro (fun=>_) m (ex_intro (fun=>_) d H))=>{m d}H.
  move: Li Lr H; apply/paco2_acc=> r _.
  move=>/(_ _ _ (ex_intro _ _ (ex_intro _ _ (conj erefl _ ))))-CIH Li Lr.
  move=>[m][n][<-]{Li}; case: n=>//= n LE.
  apply/paco2_fold; constructor; move: LE; case: (boolP (n == m)).
  - move=>/eqP-> _; rewrite lopen_nrec add0n eq_refl.
    rewrite -/(n_rec m.+1 _) lshift_nrec // nrec_twice addnS.
    by right; apply/CIH; apply: leq_addr.
  - move=> H0 H1; move: {H0 H1} (conj H0 H1)=>/andP.
    rewrite eq_sym -ltn_neqAle => LE; rewrite lopen_bound //.
    by right; apply/CIH.
Qed.

Fixpoint expand_env (e : seq (role * l_ty)) : {fmap role -> rl_ty} :=
  match e with
  | [::] => [fmap]
  | (k, v) :: t => (expand_env t).[k <- l_expand v]
  end%fmap.

Lemma in_expanded_env (e : seq (role * l_ty)) p :
  (omap l_expand (find_cont e p) = (expand_env e).[? p])%fmap.
Proof.
  elim: e=>//=; first by rewrite fnd_fmap0.
  move=>[k v] t; rewrite fnd_set /extend; case: ifP=>[/eqP->|neq].
  + by rewrite eq_refl.
  + by rewrite eq_sym neq.
Qed.

Lemma lunroll_isend L CL : LUnroll L CL -> l_isend L -> CL = rl_end.
Proof.
  move=> LU /keep_unrolling-[k END]; move: LU=>/(LUnroll_ind k).
  by move: END=><-; apply/lunroll_end.
Qed.
