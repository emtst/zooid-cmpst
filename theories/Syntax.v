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

Module TpEntry : ENTRY.
  Definition K := atom_eqType.
  Definition V := tp_eqType.
End TpEntry.

Module TpEnv := Env TpEntry.
Module TpLemmata := Lemata TpEntry TpEnv.

Check TpLemmata.eq_hd.


(* DC: tentative LN representation of global types *)

(* Set of labels: FIXME - atoms? *)
Definition lbl := nat.

(* Set of participants : FIXME - atoms? *)
Definition part:= nat.

Inductive g_type : Set :=
| g_end : g_type
| g_fvar : atom -> g_type
| g_bvar : nat -> g_type
| g_rec : g_type -> g_type
| g_msg : part -> part -> seq (lbl * tp * g_type) -> g_type.


Inductive l_type : Set :=
| l_end : l_type
| l_fvar : atom -> l_type
| l_bvar : nat -> l_type
| l_rec : g_type -> l_type
| l_send : part -> lbl -> tp -> l_type -> l_type
| l_recv : part -> seq (lbl * tp * l_type) -> l_type.