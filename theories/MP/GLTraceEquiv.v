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
    forall a, exists G' P', step a G G' <-> lstep a P P'.

  Definition trace_equiv G P :=
    forall a, exists G' P', g_lts a G G' <-> l_lts a P P'.

  Fixpoint add_head p (Q : MsgQ) :=
    match Q with
    | [::] => [:: (p.1, [:: p.2])]
    | h :: t => if h.1 == p.1 then (h.1, p.2 :: h.2) :: t
                else h :: add_head p t
    end.

  Notation msg m := (m.1, inr m.2).
  Notation lab m l := (m.1, inl l).

  Fixpoint q_proj G (p : role) : option (MsgQ * l_ty):=
    match G with
    | rg_end => Some ([::], l_end)
    | rg_msg m G =>
      match q_proj G p with
      | Some QP => if m.snd == m.rcv then None
                   else if m.snd == p
                        then Some (QP.1, l_send m.rcv m.typ QP.2)
                        else if m.rcv == p
                             then Some (QP.1, l_recv m.snd m.typ QP.2)
                             else Some QP
      | None => None
      end
    | rg_rcv m G =>
      match q_proj G p with
      | Some QP => if m.snd == m.rcv then None
                   else if m.snd == p
                        then Some (add_head (msg m) QP.1, QP.2)
                        else if m.rcv == p
                             then Some (QP.1, l_recv m.snd m.typ QP.2)
                             else Some QP
      | None => None
      end
        (* )
    | rg_brn m K =>
      let KL := map (fun X => (X.1, q_proj X.2 r)) K in
    if m.snd == m.rcv
    then None
    else if m.snd == p
         then ml_sel q K
         else if q == r
              then ml_brn p K
              else merge_all K.

      match q_proj G p with
      | Some QP => if m.snd == m.rcv then None
                   else if m.snd == p
                        then Some (add_head (msg m) QP.1, QP.2)
                        else if m.rcv == p
                             then Some (QP.1, l_recv m.snd m.typ QP.2)
                             else Some QP
      | None => None
      end
    | g_brn p K =>
      let KL := map (fun X => (X.1, project X.2 r)) K in
      project_brn p r KL *)
    | _ => None
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

  Definition q_union (Q1 Q2 : MsgQ) := Q1 ++ Q2.

  Fixpoint q_project G ps :=
    match ps with
    | [::] => Some ([::], [::])
    | h :: t => match q_proj G h , q_project G t with
                | Some (Q', L), Some (Q, P) => Some (q_union Q Q', (h, L) :: P)
                | _, _ => None
                end
    end.

  Definition q_projection G :=
    q_project G (rg_parts G).

  Lemma g_trequiv G :
    forall P,
    q_projection G == Some P ->
    trace_equiv G P.
  Admitted.

  Theorem global_local_trequiv G :
    forall P,
    projection G == Some P ->
    trace_equiv (init G) ([::], P).
  Admitted.

End TraceEquiv.
