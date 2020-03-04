From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

From Paco Require Import paco paco2.

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
    forall Lb Ty L', F Lb = Some (Ty, L') -> EqL L' L.*)
 



(*In the following there is a problem, I think. However it is monotone...
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
  Hint Constructors qProj_.
  Lemma Proj_monotone : monotone2 qProj_.
  Proof.
  rewrite /monotone2; move=> x0 x1 r r' it LE; move: it; case=>//.
  + move=> p p' CONT l Ty G Q neq CONTeq rel; apply: (qprj_none neq CONTeq).
    by apply (LE _ _ rel).
  + move=> p p' CONT l Ty G Q neq CONTeq rel; apply: (qprj_some neq CONTeq).
    by apply (LE _ _ rel).
  Qed. *)

(* first version: probably wrong.

  Definition qproj_rel := rg_ty -> {fmap role * role -> seq (lbl * mty) } -> Prop.
  Inductive qProj_ (r : qproj_rel) : qproj_rel :=
  | qprj_end : qProj_ r rg_end ([fmap qq:PAR2 => [::]])
  | qprj_none p p' CONT l Ty G Q:
      p != p' -> CONT l = Some (Ty, G) ->
      r (rg_msg (Some l) p p' CONT) Q ->
      qProj_ r (rg_msg None p p' CONT) Q
  | qprj_some p p' CONT l Ty G Q:
      p != p' -> CONT l = Some (Ty, G) ->
      r G (enq Q (p,p') (l, Ty)) ->
      qProj_ r (rg_msg (Some l) p p' CONT) Q
  .
  Hint Constructors qProj_.
  Lemma qProj_monotone : monotone2 qProj_.
  Proof.
  rewrite /monotone2; move=> x0 x1 r r' it LE; move: it; case=>//.
  + move=> p p' CONT l Ty G Q neq CONTeq rel; apply: (qprj_none neq CONTeq).
    by apply (LE _ _ rel).
  + move=> p p' CONT l Ty G Q neq CONTeq rel; apply: (qprj_some neq CONTeq).
    by apply (LE _ _ rel).
  Qed.
  Definition qProject CG Q := paco2 (qProj_) bot2 CG Q.*)

  Definition qproj_rel := rg_ty -> {fmap role * role -> seq (lbl * mty) } -> Prop.
  Inductive qProj_ (r : qproj_rel) : qproj_rel :=
  | qprj_end : qProj_ r rg_end ([fmap qq:PAR2 => [::]])
  | qprj_none p p' CONT l Ty G Q Q':
      p != p' -> CONT l = Some (Ty, G) ->
      (*deq Q (p, p') == Some ((l, Ty), Q') ->*)
      Q == enq Q' (p, p') (l, Ty) ->
      r (rg_msg (Some l) p p' CONT) Q ->
      qProj_ r (rg_msg None p p' CONT) Q'
  | qprj_some p p' CONT l Ty G Q Q':
      p != p' -> CONT l = Some (Ty, G) ->
      (*Q' == (enq Q (p,p') (l, Ty)) ->*)
      deq Q' (p, p') == Some ((l, Ty), Q) ->
      r G Q ->
      qProj_ r (rg_msg (Some l) p p' CONT) Q'
  .
  Hint Constructors qProj_.
  Lemma qProj_monotone : monotone2 qProj_.
  Proof.
  rewrite /monotone2; move=> x0 x1 r r' it LE; move: it; case=>//.
  + move=> p p' CONT l Ty G Q Q' neq CONTeq dequ rel.
    apply: (qprj_none neq CONTeq dequ); by apply (LE _ _ rel).
  + move=> p p' CONT l Ty G Q Q' neq CONTeq enqu rel.
    apply: (qprj_some neq CONTeq enqu); by apply (LE _ _ rel).
  Qed.
  Hint Resolve qProj_monotone.
  Definition qProject CG Q := paco2 (qProj_) bot2 CG Q.

About Project.

Open Scope fmap.

(*
translate p to something in the domain of L ()
*)
  Definition eProject (G: rg_ty) (E : {fmap role -> rl_ty}) : Prop :=
  (forall p L, Project p G L -> E.[? p] = Some L).



(*L to D and F; about the next 4 lemmas:
  - should be moved
  - might be be turned into 2 or even 0
*)
  Lemma qProject_None_exists_aux F T C Q GG: 
    GG = (rg_msg None F T C) ->
    qProject GG Q -> 
    F != T /\
    (exists l Ty G Q',
    C l = Some (Ty, G) /\
    (*deq Q' (F, T) == Some ((l, Ty), Q) /\*)
    Q' == enq Q (F, T) (l, Ty) /\
    qProject (rg_msg (Some l) F T C) Q').
  Proof.
  move=> eq hp; punfold hp.
  move: hp eq => [ | p p' CONT l Ty G {}Q Q' H0 H1 H2 H3| ]//= [].
  move=> H4 H5 H6; split; [by rewrite -H4 -H5 | exists l, Ty, G, Q].
  split; [by rewrite -H1 H6 | split; [by rewrite -H4 -H5|]].
  by move: H3; rewrite H4 H5 H6 /upaco2 /qProject /bot2; elim.
  Qed.

  Lemma qProject_None_exists F T C Q:
    qProject (rg_msg None F T C) Q -> 
    F != T /\
    (exists l Ty G Q',
    C l = Some (Ty, G) /\
    (*deq Q' (F, T) == Some ((l, Ty), Q) /\*)
    Q' == enq Q (F, T) (l, Ty) /\
    qProject (rg_msg (Some l) F T C) Q').
  Proof.
  by apply: qProject_None_exists_aux.
  Qed.



  Lemma qProject_Some_exists_aux l F T C Q GG: 
    GG = (rg_msg (Some l) F T C) ->
    qProject GG Q -> 
    F != T /\
    (exists Ty G Q',
    C l = Some (Ty, G) /\
    (*Q == (enq Q' (F,T) (l, Ty)) /\*)
    deq Q (F, T) == Some ((l, Ty), Q') /\
    qProject G Q').
  Proof.
  move=> eq hp; punfold hp.
  move: hp eq  => [| | p p' CONT l0 Ty G {}Q Q' H0 H1 H2 H3] //= [].
  move=> H4 H5 H6 H7. split; [by rewrite -H5 -H6 | exists  Ty, G, Q].
  split; [by rewrite -H1 H7 H4 | split; [ by rewrite -H5 -H6 -H4|]].
  by move: H3; rewrite /upaco2 /qProject /bot2; elim.
  Qed.

  Lemma qProject_Some_exists l F T C Q:
    qProject (rg_msg (Some l) F T C) Q -> 
    F != T /\
    (exists Ty G Q', C l = Some (Ty, G) /\
    (*Q == (enq Q' (F,T) (l, Ty)) /\*)
    deq Q (F, T) == Some ((l, Ty), Q') /\
    qProject G Q').
  Proof.
  by apply: qProject_Some_exists_aux.
  Qed.


  (*Lemma step_qProject_send F T C L Ty Q:
    step (a_send F T L Ty) (rg_msg None F T C) (rg_msg (Some L) F T C) ->
    qProject (rg_msg None F T C) Q ->
    F != T /\ (exists G Q',
    C L = Some (Ty, G) /\ Q' == enq Q (F, T) (L, Ty) /\
    qProject (rg_msg (Some L) F T C) Q').
  Proof.

  move=> ste qpro; split; [ by move: (qProject_None_exists qpro); elim |].
  
  Admitted.*)


  Lemma qProject_step G Q E a G':
  step a G G' -> qProject G Q -> eProject G E
    -> exists E' Q', lstep a (E, Q) (E', Q').
  Proof.
  elim.
  + move=> L F T C Ty G0 contL qpro epro.
    move: (qProject_None_exists qpro); elim; move=> rneq.
    elim; move=>x; elim.
  Admitted.




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
