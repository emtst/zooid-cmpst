From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Atom.
Require Import MPST.AtomSets.
Require Import MPST.Forall.
Require Import MPST.LNVar.
Require Import MPST.Global.
Require Import MPST.Local.
Require Import MPST.Actions.
Require Import MPST.Projection.

Section TraceEquiv.

(*Finite set to be thought of as the set of all participants involved in the protocol.*)
Variable PAR : {fset role}.

Definition PAR2 := (PAR `*` PAR)%fset.


  (*Definition Merge (F : lbl /-> mty * rl_ty) (L : rl_ty) : Prop :=
    forall Lb Ty L', F Lb = Some (Ty, L') -> EqL L' L.

  Definition proj_rel := rg_ty -> rl_ty -> Prop.
  Inductive Proj_ (p : role) (r : proj_rel) : proj_rel :=
  | prj_end : Proj_ p r rg_end rl_end
  | prj_send1 q KsG KsL :
      p != q ->
      R_all r KsG KsL ->
      Proj_ p r (rg_msg None p q KsG) (rl_msg l_send q KsL)
  | prj_send2 l t q KsG KsL L :
      p != q ->
      R_all r KsG KsL ->
      KsL l = Some (t, L) ->
      Proj_ p r (rg_msg (Some l) p q KsG) L
  | prj_recv o q KsG KsL :
      p != q ->
      R_all r KsG KsL ->
      Proj_ p r (rg_msg o q p KsG) (rl_msg l_recv q KsL)
  (* | prj_end2 G : ~ In r G -> Proj_ r G rl_end *)
  | prj_mrg o q s KsG KsL L :
      q != s ->
      p != q ->
      p != s ->
      (* InAll r KsG -> *)
      R_all r KsG KsL ->
      Merge KsL L ->
      Proj_ p r (rg_msg o q s KsG) L
  .
  Hint Constructors Proj_.
  Lemma Proj_monotone p : monotone2 (Proj_ p).
  Proof.
  rewrite /monotone2; move=> x0 x1 r r' it LE; move: it; case=>//.
  + move=> q KsG KsL neq HP; constructor =>//; move: HP; rewrite /R_all.
    move=> HP l Ty G L KsG_l KsL_l; apply: LE; by apply: (@HP l Ty G L KsG_l KsL_l).
  + move=> l t q KsG KsL L neq HP KsL_l; apply: (@prj_send2 _ _ l t _ _ KsL) => //.
    move: HP; rewrite /R_all; move=> HP l0 t0 G0 L0 KsG_l0 KsL_l0; apply LE.
    by apply: (@HP l0 _ _ _ KsG_l0 KsL_l0).
  + move=> o q KsG KsL neq HP; constructor =>//; move: HP; rewrite /R_all.
    move=> HP l t G L KsG_l KsL_l; apply: LE. by apply: (HP _ _ _ _ KsG_l KsL_l).
  + move=> o q s KsG KsL L0 neq_qs neq_pq neq_ps HP merg.
    apply (@prj_mrg _ _ _ _ _ KsG KsL _) =>//; move: HP; rewrite /R_all.
    move=> HP l t G L KsG_l KsL_l; apply: LE; by apply: (HP _ _ _ _ KsG_l KsL_l).
  Qed.
  Definition Project p CG CL := paco2 (Proj_ p) bot2 CG CL.*)



(*In the following there is definitely a problem. And I believe the problem is of monotonicity.*)
  Definition qproj_rel := rg_ty -> {fmap role * role -> seq (lbl * mty) } -> Prop.
  Inductive qProj_ (*p p': role*) (r : qproj_rel) : qproj_rel :=
  | qprj_end : qProj_ r rg_end ([fmap qq:PAR2 => [::]])
  | qprj_none q q' CONT l Ty G Q:
      q != q' -> CONT l = Some (Ty, G) ->
      r (rg_msg None q q' CONT) Q ->
      qProj_ r (rg_msg (Some l) q q' CONT) Q
  | qprj_some q q' CONT l Ty G Q:
      q != q' -> CONT l = Some (Ty, G) ->
      r (rg_msg (Some l) q q' CONT) Q ->
      qProj_ r G (enq Q (q,q') (l, Ty))
  .




  Definition step_equiv G P :=
    forall a, (exists G', step a G G') <-> (exists P', lstep a P P').

  Fail Lemma g_stequiv G E Q :
    proj_cfg G == Some (E, Q) ->
    step_equiv G (E, Q).
  (*
  Proof.
    rewrite /step_equiv/proj_cfg.
    case G_E: (proj_env G) => [E'|//].
    case G_Q: (queue_contents G [fmap]%fmap) => [Q'|//].
    move=>/eqP=>[[EE' QQ']].
    move: EE' QQ' G_E G_Q=>->->/eqP-H1/eqP-H2 a; split.
    (* Testing *)
    move=>[G']. elim=>//.
    About step_ind1.
    (* End Testing *)
    - move=>[G' H]; move: G H H1 H2; elim/gty_ind1=>//.
      + by move=> St; case Eq: (g_end (option lbl)) _ / St =>//.
      + by move=> v St; case Eq: (g_var (option lbl) v) _ / St =>//.
      + move=> G Ih.
        admit.
      + move=> lb p q Ks Ih.
        admit.
        (*
        move=> lb p q Ks t Gp Cont Proj Queue.
        move: (proj_send Proj) => [KsL] /andP-[Ks_KsL E_KsL].
        move: (lookup_prjall Cont Ks_KsL) => [Lp /andP-[Gp_Lp KsL_Lp]].
        move: (doact_send E_KsL KsL_Lp) => [E'' E_send].
        by exists (E'', enq Q (p, q) (lb, t)); constructor.
         *)
    - admit.
  Admitted.
   *)

  (*
  Inductive Roll : renv -> renv -> Prop :=
  | RR : forall p P Q,

  Definition trace_equiv G P : Prop :=
    forall tr, g_lts tr G <-> l_lts tr P.

   *)
  Fail Lemma g_trequiv G : forall P, proj_cfg G == Some P -> trace_equiv G P.
  (*
  Proof.
    move=>[E Q]; rewrite /trace_equiv/proj_cfg.
    case G_E: (proj_env G) => [E'|//].
    case G_Q: (queue_contents G [fmap]%fmap) => [Q'|//].
    move=>/eqP=>[[EE' QQ']].
    move: EE' QQ' G_E G_Q=>->->/eqP-H1/eqP-H2 tr; split.

    cofix Ch.
    + move=> trcG; move: trcG H1 H2 Ch; case.
      * rewrite /proj_env/= =>/eqP-[<-] /eqP-[<-] _; constructor.
      * move=> a t G0 G' step trc.
      * move=>/=. _.
   *)

  Fail Definition q_projection G :=
    if is_valid G then q_project G (rg_parts G)
    else None.

  Fail Lemma g_stequiv G :
    forall (P : MsgQ * seq (role * l_ty)),
    Projection G P ->
    step_equiv G P.
  (*
  Proof.
    rewrite /step_equiv/Projection => [[Q P]/= [Parts G_P] a]; split.
    - move=> [G' H]; move: H Parts G_P; elim =>///=.
      - move=>[[p q] ty]/= {G}G Parts.
      (* Lemmas about q_projection to simplify these proofs: e.g.
         if q_projection (rg_msg p G) == Some (Q, P) ->
            msg_proj G p == Some Qp &&
            msg_proj G q == Some Qq &&
            Q == Qp ++ Qq &&
            q_proj G p == Some Lp &&
            q_proj G q == Some Lq &&
            q_projection G == Some (Q', P') &&
            Q == Qp ++ Qq ++ Q' &&
            P == (p, Lp) :: (q, Lq) :: Some (Q', P')

          Maybe the better option is to reflect q_projection as an inductive
          predicate relating
      *)
      admit.
    - move=> [[Q' P']].
      admit.
  Admitted.
   *)

  (*
  Lemma st_valid a G G' :
    is_valid G -> step a G G' -> is_valid G'.
  Proof.
  Admitted.
   *)

  Fail Lemma g_stproj a G G' :
    forall (P P' : MsgQ * seq (role * l_ty)),
    q_projection G == Some P ->
    step a G G' ->
    lstep a P P' ->
    q_projection G' == Some P'.
  (*
  Proof.
  Admitted.
   *)

  Fail Lemma qproj_end G :
    q_projection G == Some ([::], [::]) ->
    G = rg_end.
  (*
  Proof.
    rewrite /q_projection.
    elim: {-1} (rg_parts G) (eq_refl (rg_parts G)) =>//.
    + elim/rgty_ind2: G=>///= G; case: (is_valid G) =>//.
      by move=> Ih /Ih/(_ (eq_refl _))->; rewrite eq_refl.
    + move=> p rs Ih/= _.
      case: (is_valid G); case: (q_proj G p); case: (q_project G rs) =>//.
      - move=>[Q P] [Q' L] /eqP-[QQ]; case: P=>// [l' L'].
        by rewrite /insert/=; case: ifP=>/=// _; case: (lookup p L').
      - by move=>[Q P].
  Qed.
   *)

  Fail Lemma g_trequiv G :
    forall (P : MsgQ * seq (role * l_ty)),
    q_projection G == Some P ->
    trace_equiv G P.
  (*
  Proof.
  (*   move=> P H; rewrite /trace_equiv=> tr; split. *)
  (*   - move: tr G P H; cofix Ch; move=> tr G P H; case: tr. *)
  (*     + move=> H1; elim/glts_inv: H1=>// _ _ Eq; move: Eq H=><-/=. *)
  (*       by rewrite /q_projection/==>/eqP-[<-]; constructor. *)
  (*     + move=> a t; elim/glts_inv=>// _ a' t' G0 G' aG tG' [aa' tt' _ {G0}]. *)
  (*       move: aa' aG=>->aG {a'}. *)
  (*       move: tt' tG'=>->tG' {t'}. *)
  (*       move: (g_stequiv H) => /(_ a)-[/(_ (ex_intro _ G' aG))-[P' PP'] _]. *)
  (*       apply: lt_next; [apply: PP'| apply: Ch]; last (by apply: tG'). *)
  (*       by apply: (g_stproj H aG). *)
  (*   - move: tr G P H; cofix Ch; move=> tr G P H; case: tr. *)
  (*     + move=> H1; elim/llts_inv: H1=>// _ _ Eq; move: Eq H=><-/=. *)
  (*       by move=>/qproj_end->; apply: eg_end. *)
  (*     + move=> a t; elim/llts_inv=>// _ a' t' P0 P' aP tP' [aa' tt' _ {P0}]. *)
  (*       move: aa' aP=>->aP {a'}. *)
  (*       move: tt' tP'=>->tP' {t'}. *)
  (*       move: (g_stequiv H) => /(_ a)-[_ /(_ (ex_intro _ P' aP))-[G' GG']]. *)
  (*       apply: eg_trans; [apply: GG'| apply: Ch]; last (by apply: tP'). *)
  (*       by apply: (g_stproj H GG'). *)
  (* Qed. *)
  Admitted.
   *)

  Fail Lemma rgparts_init G :
    rg_parts (init G) = participants G.
  (*
  Proof.
    elim/gty_ind2: G=>/=//.
    + by move=> [[p q] ty] G/=->.
    + move=> [[p q] ty] Gs /=/forall_member-Ih; do ! (congr cons).
      congr seq.flatten; rewrite -map_comp/comp/=.
      by apply/Fa_map_eq/forall_member => lG /(Ih lG).
  Qed.
   *)

  Fail Lemma msg_project_init G p :
    msg_proj (init G) p = Some [::].
  (*
  Proof.
    elim/gty_ind2: G=>// pr K Ih/=; rewrite -map_comp/comp/=.
    move: Ih; case: K=>[//|[l G] K/= [->]/=].
    by elim: K=>[//|[l1 G1] K/= Ih [-> /Ih->]].
  Qed.
   *)

  Fail Lemma rg_project_init G p :
    rg_proj (init G) p = project G p.
  (*
  Proof.
    elim/gty_ind2: G=>///=.
    - by move=>G->.
    - by move=>pr G ->.
    - move=>pr K /forall_member-Ih; rewrite -map_comp/comp/=; congr project_brn.
      by apply/Fa_map_eq/forall_member => x xK; move: (Ih x xK)=>->.
  Qed.
   *)

  Fail Lemma gvalid_isvalid G :
    is_valid (init G) = g_valid G.
  (*
  Admitted.
   *)

  Fail Lemma project_init G P :
    projection G == Some P -> q_projection (init G) = Some ([::], P).
  (*
  Proof.
    rewrite /projection/q_projection rgparts_init gvalid_isvalid.
    case: (g_valid G) =>//; elim: (participants G) P.
    - by move=>P /eqP-[<-].
    - move=> a ps Ih/= P.
      rewrite /q_proj msg_project_init rg_project_init option_comm.
      case: (project G a)=>// L.
      by move: Ih; case: (project_all G ps) =>// K /(_ K (eq_refl _))-> /eqP-[->].
  Qed.
   *)

  Fail Theorem global_local_trequiv G :
    forall P,
    projection G == Some P ->
    trace_equiv (init G) ([::], P).
  (*
  Proof. by move=>P /project_init/eqP; apply g_trequiv. Qed.
   *)

End TraceEquiv.

(* Validity of global types without participants missing, plus related lemmas
 * We need that, if valid G and step a G G', then valid G'

Print Assumptions global_local_trequiv.
 *)
