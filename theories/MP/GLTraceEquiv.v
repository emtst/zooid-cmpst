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

  Definition trace_equiv G P :=
    forall a, (exists G', g_lts a G G') <-> (exists P', l_lts a P P').

  Fixpoint add_head p (Q : MsgQ) :=
    match Q with
    | [::] => [:: (p.1, [:: p.2])]
    | h :: t => if h.1 == p.1 then (h.1, p.2 :: h.2) :: t
                else h :: add_head p t
    end.

  Notation msg m := (m.1, inr m.2).
  Notation lab m l := (m.1, inl l).

  Fixpoint merge_mq (Q : MsgQ) (Qs : seq MsgQ) :=
    match Qs with
    | [::] => Some Q
    | h :: t => if h == Q then merge_mq Q t
                else None
    end.

  Definition merge_q (Q : seq MsgQ) :=
    match Q with
    | [::] => Some [::]
    | h :: t => merge_mq h t
    end.

  Print project.

  Fixpoint q_proj G (p : role) : option (MsgQ * l_ty):=
    match G with
    | rg_end => Some ([::], l_end)
    | rg_var v => Some ([::], l_var v)
    | rg_rec G =>
      match q_proj G p with
      | Some (Q, P) =>
        if P == l_var (Rvar.bv 0) then None else Some (Q, l_rec P)
      | None => None
      end
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
    | rg_brn m K =>
      match
        (fix q_projK K : option (seq MsgQ * seq (lbl * l_ty)):=
           match K with
           | [::] => Some ([::], [::])
           | lG :: K =>
             match q_proj lG.2 p, q_projK K with
             | Some QP, Some QK =>
                 Some (QP.1 :: QK.1, (lG.1, QP.2) :: QK.2)
             | _, _ => None
             end
           end
        ) K
      with
      | None => None
      | Some (Q, K) =>
        match merge_q Q with
        | None => None
        | Some Q =>
          if m.snd == m.rcv then None
          else if m.snd == p
               then Some (Q, l_sel m.rcv K)
               else if m.rcv == p
                    then Some (Q, l_brn m.snd K)
                    else match K with
                         | [::] => None
                         | h :: t => if all (fun X => h.2 == X.2) t
                                     then Some (Q, h.2)
                                     else None
                         end
        end
      end
    | rg_alt lb m K =>
      match
        (fix q_projK K : option (seq MsgQ * seq (lbl * l_ty)):=
           match K with
           | [::] => Some ([::], [::])
           | lG :: K =>
             match q_proj lG.2 p, q_projK K with
             | Some QP, Some QK =>
                 Some (QP.1 :: QK.1, (lG.1, QP.2) :: QK.2)
             | _, _ => None
             end
           end
        ) K
      with
      | None => None
      | Some (Q, K) =>
        match merge_q Q, lookup lb K with
        | Some Q, Some G =>
          if m.snd == m.rcv then None
          else if m.snd == p
               then Some (add_head (lab m lb) Q, G)
               else if m.rcv == p
                    then Some (Q, l_brn m.snd K)
                    else match K with
                         | [::] => None
                         | h :: t => if all (fun X => h.2 == X.2) t
                                     then Some (Q, h.2)
                                     else None
                         end
        | _, _ => None
        end
      end
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

  Definition q_projection G :=
    q_project G (rg_parts G).

  Lemma g_trequiv G :
    forall (P : MsgQ * seq (role * l_ty)),
    q_projection G == Some P ->
    trace_equiv G P.
  Proof.
    rewrite /q_projection/trace_equiv.
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


  Lemma project_init G P :
    projection G == Some P -> q_projection (init G) = Some ([::], P).
  Proof.
    rewrite /projection/q_projection rgparts_init; elim: (participants G) P.
    - by move=>P /eqP-[<-].
    - move=> a ps Ih/= P.
      suff: forall L, project G a == Some L ->
                      q_proj (init G) a == Some ([::], L).
      {
        case: (project G a)=>/=// L' /(_ L').
        rewrite eq_refl=>/(_ is_true_true) =>/eqP->.
        case: P=>//; first (by case: (project_all G ps)).
        move=> lG P; move: (Ih P); case: (project_all G ps) =>// P' {Ih}H.
        by move=>/eqP-[-> PP']; move: PP' H =>-> /(_ (eq_refl _))->/=.
      }
      move=> {Ih P ps}.
      elim/gty_ind2: G=>//.
      + move=> G Ih L/=; move: Ih.
        case: (project G a)=>// L' /(_ L' (eq_refl _))/eqP->/=.
        by rewrite -[Some _ == Some _]/(L' == _); case: ifP.
      + move=> [[p q] ty] G/=; rewrite /ml_send/ml_recv.
        case: (ifP (p == q))=>//.
        case: (project G a) =>//;
          last (by case: (ifP (p == a))=>//; case: (ifP (q == a))).
        move=>L _ /(_ L (eq_refl _)) /eqP-> L'/=.
        by (do ! case: ifP=>//).
      + move=> [[p q] ty] K Ih/= L.
  Admitted. (* TODO: Fix q_proj to simplify proof *)

  Theorem global_local_trequiv G :
    forall P,
    projection G == Some P ->
    trace_equiv (init G) ([::], P).
  Proof. by move=>P /project_init/eqP; apply g_trequiv. Qed.

End TraceEquiv.
