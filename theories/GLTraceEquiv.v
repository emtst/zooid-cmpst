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
Require Import MPST.Projection.

Section TraceEquiv.

  Definition step_equiv G P :=
    forall a, (exists G', step a G G') <-> (exists P', lstep a P P').

  Definition trace_equiv G P : Prop :=
    forall tr, g_lts tr G <-> l_lts tr P.

  Fixpoint add_head p (Q : MsgQ) :=
    match Q with
    | [::] => [:: (p.1, [:: p.2])]
    | h :: t => if h.1 == p.1 then (h.1, p.2 :: h.2) :: t
                else h :: add_head p t
    end.

  Notation msg m := (m.1, inr m.2).
  Notation lab m l := (m.1, inl l).

  Fixpoint merge_mq (Q : MsgQ) (Qs : seq (option MsgQ)) :=
    match Qs with
    | [::] => Some Q
    | h :: t => if h == Some Q then merge_mq Q t
                else None
    end.

  Definition merge_q (Q : seq (option MsgQ)) :=
    match Q with
    | [::] => Some [::]
    | h :: t =>
      match h with
      | Some q => merge_mq q t
      | None => None
      end
    end.

  Fixpoint msg_proj G (p : role) : option MsgQ :=
    match G with
    | rg_end
    | rg_var _ => Some [::]
    | rg_msg _ G
    | rg_rec G => msg_proj G p
    | rg_rcv m G =>
      if m.snd == p
      then match msg_proj G p with
           | Some Q => Some (add_head (msg m) Q)
           | None => None
           end
      else msg_proj G p
    | rg_brn m K =>
      merge_q [seq msg_proj lG.2 p | lG <- K]
    | rg_alt lb m K =>
      if m.snd == p
      then match merge_q [seq msg_proj lG.2 p | lG <- K] with
           | Some Q => Some (add_head (lab m lb) Q)
           | None => None
           end
      else merge_q [seq msg_proj lG.2 p | lG <- K]
    end.

  Definition project_rcv p r L :=
    let: (p1, q, t) := p in
    if p1 == q
    then None
    else if q == r
         then ml_recv p1 t L
         else L.

  Definition project_alt (p : g_prefix) (r : role) (K : seq (lbl * option l_ty)) :=
    let: ((p, q), t) := p in
    if p == q
    then None
    else if q == r
         then ml_brn p K
         else merge_all K.

  Notation lbv v := (l_var (Rvar.bv 0)).

  Fixpoint rg_proj G (r : role) : option l_ty :=
    match G with
    | rg_end => Some l_end
    | rg_var v => Some (l_var v)
    | rg_rec G => let: L := rg_proj G r in
                  if L == Some (lbv 0) then None else ml_rec L
    | rg_rcv m G => project_rcv m r (rg_proj G r)
    | rg_msg m G => project_msg m r (rg_proj G r)
    | rg_brn p K => let: KL := [seq (X.1, rg_proj X.2 r) | X <- K]
                    in project_brn p r KL
    | rg_alt lb p K => let: KL := [seq (X.1, rg_proj X.2 r) | X <- K]
                       in project_alt p r KL
    end.

  Definition q_proj G r :=
    match msg_proj G r, rg_proj G r with
    | Some Q, Some L => Some (Q, L)
    | _, _ => None
    end.

  Inductive mq_proj p : rg_ty -> MsgQ -> l_ty -> Prop :=
  | prj_end :
      mq_proj p rg_end [::] l_end
  | prj_var  v :
      mq_proj p (rg_var v) [::] (l_var v)
  | prj_rec G Q L :
      L != lbv 0 ->
      mq_proj p G Q L ->
      mq_proj p (rg_rec G) Q (l_rec L)
  | prj_msg1 q x G Q L :
      p != q ->
      mq_proj p G Q L ->
      mq_proj p (rg_msg ((p, q), x) G) Q (l_send q x L)
  | prj_msg2 q x G Q L :
      p != q ->
      mq_proj p G Q L ->
      mq_proj p (rg_msg ((q, p), x) G) Q (l_recv q x L)
  | prj_msg3 f t x G Q L :
      f != t ->
      f != p ->
      f != p ->
      mq_proj p G Q L ->
      mq_proj p (rg_msg ((f, t), x) G) Q L
  | prj_rcv1 q x G Q L :
      p != q ->
      mq_proj p G Q L ->
      mq_proj p (rg_rcv ((p, q), x) G) (add_head ((p, q), inr x) Q) L
  | prj_rcv2 q x G Q L :
      p != q ->
      mq_proj p G Q L ->
      mq_proj p (rg_rcv ((q, p), x) G) Q (l_recv q x L)
  | prj_rcv3 f t x G Q L :
      f != t ->
      f != p ->
      f != p ->
      mq_proj p G Q L ->
      mq_proj p (rg_rcv ((f, t), x) G) Q L
  | prj_brn1 q x KG Q KL :
      p != q ->
      proj_alts p KG Q KL ->
      mq_proj p (rg_brn ((p, q), x) KG) Q (l_sel q KL)
  | prj_brn2 q x KG Q KL :
      p != q ->
      proj_alts p KG Q KL ->
      mq_proj p (rg_brn ((q, p), x) KG) Q (l_brn q KL)
  | prj_brn3 f t x KG Q L :
      f != t ->
      f != p ->
      p != t ->
      proj_all p KG Q L ->
      mq_proj p (rg_brn ((f, t), x) KG) Q L
  | prj_alt1 l q x KG Q KL L :
      p != q ->
      lookup l KL == Some L ->
      proj_alts p KG Q KL ->
      mq_proj p (rg_alt l ((p, q), x) KG) (add_head ((p, q), inl l) Q) L
  | prj_alt2 l q x KG Q KL :
      p != q ->
      proj_alts p KG Q KL ->
      mq_proj p (rg_alt l ((q, p), x) KG) Q (l_brn q KL)
  | prj_alt3 l f t x KG Q L :
      f != t ->
      f != p ->
      p != t ->
      proj_all p KG Q L ->
      mq_proj p (rg_alt l ((f, t), x) KG) Q L
  with
  proj_alts p : seq (lbl * rg_ty) -> MsgQ -> seq (lbl * l_ty) -> Prop :=
  | prj_nil G Q L l :
      mq_proj p G Q L ->
      proj_alts p [:: (l, G)] Q [:: (l, L)]
  | prj_cons KG Q KL l G L :
      mq_proj p G Q L ->
      proj_alts p KG Q KL ->
      proj_alts p ((l, G) :: KG) Q ((l, L) :: KL)
  with
  proj_all p : seq (lbl * rg_ty) -> MsgQ -> l_ty -> Prop :=
  | prj_all_nil G Q L l :
      mq_proj p G Q L ->
      proj_all p [:: (l, G)] Q L
  | prj_all_cons KG Q l G L :
      mq_proj p G Q L ->
      proj_all p KG Q L ->
      proj_all p ((l, G) :: KG) Q L.

  Derive Inversion mqproj_inv with (forall p G Q L, mq_proj p G Q L) Sort Prop.
  Derive Inversion mqproj_end_inv with (forall p Q L, mq_proj p rg_end Q L) Sort Prop.
  Derive Inversion mqproj_var_inv with (forall v p Q L, mq_proj p (rg_var v) Q L) Sort Prop.
  Derive Inversion mqproj_rec_inv with (forall p G Q L, mq_proj p (rg_rec G) Q L) Sort Prop.
  Derive Inversion projalts_inv with (forall p K Q L, proj_alts p K Q L) Sort Prop.
  Derive Inversion projall_inv with (forall p K Q L, proj_all p K Q L) Sort Prop.

  Lemma qproj_equiv p G Q L : q_proj G p == Some (Q, L) <-> mq_proj p G Q L.
  Proof.
    suff : (msg_proj G p == Some Q) && (rg_proj G p == Some L)
           <-> mq_proj p G Q L.
    {
      suff : (msg_proj G p == Some Q) && (rg_proj G p == Some L)
             <-> q_proj G p == Some (Q, L)
        by move=>->.
      rewrite /q_proj; split; case: (msg_proj G p); case: (rg_proj G p)=>//Q'.
      by rewrite andbC.
    }
    move: G Q L; elim/rgty_ind2 =>///=.
    - move=> Q L; rewrite /q_proj/=; split.
      + by move=>/andP-[/eqP-[<-] /eqP-[<-]]; constructor.
      + by elim/mqproj_end_inv.
    - move=> v Q L; rewrite /q_proj/=; split.
      + by move=>/andP-[/eqP-[<-] /eqP-[<-]]; constructor.
      + by elim/mqproj_var_inv; rewrite !eq_refl.
    - move=> G Ih Q L; split.
      + move=>/andP-[GQ]; case: ifP=>// neqL; rewrite /ml_rec => H.
        have [L' GL']: exists L', rg_proj G p == Some L'
            by move: H; case: (rg_proj G p) => // L' _; exists L'.
        move: GQ GL' H neqL (Ih Q L') =>/eqP-> /eqP-> /eqP-[<-] {Ih}.
        rewrite -[Some _ == Some _]/(L' == _) (rwP negPf) !eq_refl => L'lvar.
        by move=>[/(_ is_true_true)-Ih _]; constructor.
      + elim/mqproj_rec_inv=>_ G0 Q0 L0 Neq /Ih/andP-[->/eqP->] _ _ _{G0 Q0 L}/=.
        by rewrite -[Some _ == _]/(L0 == _) (negPf Neq).
  Admitted.

  Inductive Proj G : seq role -> MsgQ * PEnv -> Prop :=
  | proj_end : Proj G [::] ([::], [::])
  | proj_next p ps Q1 Q2 L P :
      mq_proj p G Q1 L -> Proj G ps (Q2, P) ->
      Proj G (p :: ps) (Q1 ++ Q2, insert (p, L) P).

  Definition Projection G P := (forall x, x \in rg_parts G <-> x \in unzip1 P.2)
                               /\ Proj G (unzip1 P.2) P.

  Definition q_union (Q1 Q2 : MsgQ) := Q1 ++ Q2.

  Fixpoint q_project G ps :=
    match ps with
    | [::] => Some ([::], [::])
    | h :: t => match q_proj G h , q_project G t with
                | Some (Q', L), Some (Q, P) => Some (q_union Q Q', insert (h, L) P)
                | _, _ => None
                end
    end.

  Fixpoint is_valid G :=
    match G with
    | rg_var _ => false
    | rg_rec G => is_valid G && (G != rg_end)
    | _ => true
    end.

  Definition q_projection G :=
    if is_valid G then q_project G (rg_parts G)
    else None.

  Lemma g_stequiv G :
    forall (P : MsgQ * seq (role * l_ty)),
    Projection G P ->
    step_equiv G P.
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

  (*
  Lemma st_valid a G G' :
    is_valid G -> step a G G' -> is_valid G'.
  Proof.
  Admitted.
   *)

  Lemma g_stproj a G G' :
    forall (P P' : MsgQ * seq (role * l_ty)),
    q_projection G == Some P ->
    step a G G' ->
    lstep a P P' ->
    q_projection G' == Some P'.
  Proof.
  Admitted.

  Lemma qproj_end G :
    q_projection G == Some ([::], [::]) ->
    G = rg_end.
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

  Lemma g_trequiv G :
    forall (P : MsgQ * seq (role * l_ty)),
    q_projection G == Some P ->
    trace_equiv G P.
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

  Lemma rgparts_init G :
    rg_parts (init G) = participants G.
  Proof.
    elim/gty_ind2: G=>/=//.
    + by move=> [[p q] ty] G/=->.
    + move=> [[p q] ty] Gs /=/forall_member-Ih; do ! (congr cons).
      congr seq.flatten; rewrite -map_comp/comp/=.
      by apply/Fa_map_eq/forall_member => lG /(Ih lG).
  Qed.

  Lemma msg_project_init G p :
    msg_proj (init G) p = Some [::].
  Proof.
    elim/gty_ind2: G=>// pr K Ih/=; rewrite -map_comp/comp/=.
    move: Ih; case: K=>[//|[l G] K/= [->]/=].
    by elim: K=>[//|[l1 G1] K/= Ih [-> /Ih->]].
  Qed.

  Lemma rg_project_init G p :
    rg_proj (init G) p = project G p.
  Proof.
    elim/gty_ind2: G=>///=.
    - by move=>G->.
    - by move=>pr G ->.
    - move=>pr K /forall_member-Ih; rewrite -map_comp/comp/=; congr project_brn.
      by apply/Fa_map_eq/forall_member => x xK; move: (Ih x xK)=>->.
  Qed.

  Lemma gvalid_isvalid G :
    is_valid (init G) = g_valid G.
  Admitted.

  Lemma project_init G P :
    projection G == Some P -> q_projection (init G) = Some ([::], P).
  Proof.
    rewrite /projection/q_projection rgparts_init gvalid_isvalid.
    case: (g_valid G) =>//; elim: (participants G) P.
    - by move=>P /eqP-[<-].
    - move=> a ps Ih/= P.
      rewrite /q_proj msg_project_init rg_project_init option_comm.
      case: (project G a)=>// L.
      by move: Ih; case: (project_all G ps) =>// K /(_ K (eq_refl _))-> /eqP-[->].
  Qed.

  Theorem global_local_trequiv G :
    forall P,
    projection G == Some P ->
    trace_equiv (init G) ([::], P).
  Proof. by move=>P /project_init/eqP; apply g_trequiv. Qed.

End TraceEquiv.

(* Validity of global types without participants missing, plus related lemmas
 * We need that, if valid G and step a G G', then valid G'
 *)
Print Assumptions global_local_trequiv.
