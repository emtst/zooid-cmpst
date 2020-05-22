From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Atom.
Require Import MPST.LNVar.

Module roleid := NewAtom def_atom.
Notation role:=roleid.t.

Module avar := NewAtom def_atom.
Notation atom:=avar.t.

Notation rvar := (lnvar atom).

Module Lbl := NewAtom def_atom.
Notation lbl := Lbl.t.

(* Supported messages *)
Inductive mty : Type :=
| T_nat : mty
| T_bool : mty
| T_unit : mty
| T_sum : mty -> mty -> mty
| T_prod : mty -> mty -> mty
| T_seq : mty -> mty
.

Fixpoint mty_eq (m1 m2 : mty) : bool :=
  match m1, m2 with
  | T_nat, T_nat => true
  | T_bool, T_bool => true
  | T_unit, T_unit => true
  | T_sum l1 r1, T_sum l2 r2 => mty_eq l1 l2 && mty_eq r1 r2
  | T_prod l1 r1, T_prod l2 r2 => mty_eq l1 l2 && mty_eq r1 r2
  | T_seq t1, T_seq t2 => mty_eq t1 t2
  | _, _ => false
  end.

Lemma mty_eqP t1 t2 : reflect (t1 = t2) (mty_eq t1 t2).
Proof.
  elim: t1 t2 => [|||l1 Ihl r1 Ihr|l1 Ihl r1 Ihr|t1 Ih]
                   [|||l2 r2|l2 r2| t2]/=; try by constructor.
  - case: Ihl=>[<-|E]/=; last by constructor=>[[/E]].
    case: Ihr=>[<-|E]/=; last by constructor=>[[/E]].
    by constructor.
  - case: Ihl=>[<-|E]/=; last by constructor=>[[/E]].
    case: Ihr=>[<-|E]/=; last by constructor=>[[/E]].
    by constructor.
  - case: Ih =>[<-|E]/=; last by constructor=>[[/E]].
    by constructor.
Qed.

Definition mty_eqMixin := EqMixin mty_eqP.
Canonical mty_eqType := Eval hnf in EqType mty mty_eqMixin.

Fixpoint coq_ty m :=
  match m with
  | T_nat => nat
  | T_bool => bool
  | T_unit => unit
  | T_sum l r => coq_ty l + coq_ty r
  | T_prod l r => coq_ty l * coq_ty r
  | T_seq l => seq (coq_ty l)
  end%type.

Definition g_prefix := ((role * role) * mty)%type.

(*
 Parameter mty_lbl : mty -> seq lbl.
 Parameter lbl_mty : seq lbl -> mty.
 Parameter lbl_mty_iso : forall l t, (lbl_mty l == t) = (l == mty_lbl t).
*)
