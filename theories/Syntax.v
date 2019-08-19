From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import MPST.Atom.
Require Import MPST.Env.


Inductive tp : Set :=
| Bool
.

Fixpoint eq_tp (T T': tp) : bool :=
  match T, T' with
    Bool, Bool => true
  end
.

Lemma eq_tpP : Equality.axiom eq_tp.
Proof.
  case ; case.
  by constructor.
Qed.

Canonical tp_eqMixin := EqMixin eq_tpP.
Canonical tp_eqType := Eval hnf in EqType tp tp_eqMixin.

Module TpEntry.
  Definition K := atom_eqType.
  Definition V := tp_eqType.
End TpEntry.

Module TpEnv := Env TpEntry.

Check TpEnv.def.