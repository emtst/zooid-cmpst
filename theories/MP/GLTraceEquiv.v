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
Require Import MPST.MP.Projection.

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

  Fixpoint rg_proj G (r : role) : option l_ty :=
    match G with
    | rg_end => Some l_end
    | rg_var v => Some (l_var v)
    | rg_rec G => let: L := rg_proj G r in
                  if L == Some (l_var (Rvar.bv 0)) then None else ml_rec L
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

  Definition q_union (Q1 Q2 : MsgQ) := Q1 ++ Q2.

  Fixpoint q_project G ps :=
    match ps with
    | [::] => Some ([::], [::])
    | h :: t => match q_proj G h , q_project G t with
                | Some (Q', L), Some (Q, P) => Some (q_union Q Q', (h, L) :: P)
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
    q_projection G == Some P ->
    step_equiv G P.
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
      - by move=>[Q P] [Q' L] /eqP-[].
      - by move=>[Q P].
  Qed.

  Lemma g_trequiv G :
    forall (P : MsgQ * seq (role * l_ty)),
    q_projection G == Some P ->
    trace_equiv G P.
  Proof.
    move=> P H; rewrite /trace_equiv=> tr; split.
    - move: tr G P H; cofix Ch; move=> tr G P H; case: tr.
      + move=> H1; elim/glts_inv: H1=>// _ _ Eq; move: Eq H=><-/=.
        by rewrite /q_projection/==>/eqP-[<-]; constructor.
      + move=> a t; elim/glts_inv=>// _ a' t' G0 G' aG tG' [aa' tt' _ {G0}].
        move: aa' aG=>->aG {a'}.
        move: tt' tG'=>->tG' {t'}.
        move: (g_stequiv H) => /(_ a)-[/(_ (ex_intro _ G' aG))-[P' PP'] _].
        apply: lt_next; [apply: PP'| apply: Ch]; last (by apply: tG').
        by apply: (g_stproj H aG).
    - move: tr G P H; cofix Ch; move=> tr G P H; case: tr.
      + move=> H1; elim/llts_inv: H1=>// _ _ Eq; move: Eq H=><-/=.
        by move=>/qproj_end->; apply: eg_end.
      + move=> a t; elim/llts_inv=>// _ a' t' P0 P' aP tP' [aa' tt' _ {P0}].
        move: aa' aP=>->aP {a'}.
        move: tt' tP'=>->tP' {t'}.
        move: (g_stequiv H) => /(_ a)-[_ /(_ (ex_intro _ P' aP))-[G' GG']].
        apply: eg_trans; [apply: GG'| apply: Ch]; last (by apply: tP').
        by apply: (g_stproj H GG').
  Qed.

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
