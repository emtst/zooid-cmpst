From mathcomp.ssreflect Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.AtomSets.

Inductive l_act := l_send | l_recv.

Definition dual_act a :=
  match a with
  | l_send => l_recv
  | l_recv => l_send
  end.

Create HintDb mpst.

Lemma dual_actK a : dual_act (dual_act a) = a.
Proof. by case: a. Qed.
Hint Rewrite dual_actK : mpst.

Definition eq_lact a b :=
  match a, b with
  | l_send, l_send
  | l_recv, l_recv => true
  | _, _ => false
  end.

Lemma lact_eqP : Equality.axiom eq_lact.
Proof. by rewrite /Equality.axiom => [[] []/=]; constructor. Qed.

Definition lact_eqMixin := EqMixin lact_eqP.
Canonical lact_eqType := Eval hnf in EqType l_act lact_eqMixin.


Inductive act :=
| mk_act (a : l_act) (p : role) (q : role) (l : lbl) (t : mty).

(* a trace is simply a stream of actions *)
CoInductive trace (act : Type) :=
| tr_end : trace act
| tr_next : act -> trace act -> trace act.

CoFixpoint trace_map {A B : Type} (f : A -> B) (trc : trace A) : trace B :=
  match trc with
  | tr_end => tr_end _
  | tr_next a trc => tr_next (f a) (trace_map f trc)
  end
.

Definition subject A := let: mk_act a p q _ _ := A in p.
Definition object A := let: mk_act a p q _ _ := A in q.
Definition act_ty A := let: mk_act a _ _ _ _ := A in a.
