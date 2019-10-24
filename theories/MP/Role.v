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

Parameter mty : eqType.
Parameter mty_lbl : mty -> seq lbl.
Parameter lbl_mty : seq lbl -> mty.
Parameter lbl_mty_iso : forall l t, (lbl_mty l == t) = (l == mty_lbl t).
