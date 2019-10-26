From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.MP.Atom.
Require Import MPST.MP.LNVar.

Module roleid := NewAtom def_atom.
Notation role:=roleid.t.

Module avar := NewAtom def_atom.
Notation atom:=avar.t.

Module Rvar := MkLnVar avar.
Notation rvar := Rvar.t.
Canonical rvar_eqType := Rvar.eqType.

Module Lbl := NewAtom def_atom.
Notation lbl := Lbl.t.

Definition mty := nat.

Definition g_prefix := ((role * role) * mty)%type.

Notation "p '.snd'" := (p.1.1) (at level 0).
Notation "p '.rcv'" := (p.1.2) (at level 0).
Notation "p '.typ'" := (p.2) (at level 0).
(*
 Parameter mty_lbl : mty -> seq lbl.
 Parameter lbl_mty : seq lbl -> mty.
 Parameter lbl_mty_iso : forall l t, (lbl_mty l == t) = (l == mty_lbl t).
*)
