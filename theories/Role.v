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

Definition mty := nat.

Definition g_prefix := ((role * role) * mty)%type.

(*
 Parameter mty_lbl : mty -> seq lbl.
 Parameter lbl_mty : seq lbl -> mty.
 Parameter lbl_mty_iso : forall l t, (lbl_mty l == t) = (l == mty_lbl t).
*)
