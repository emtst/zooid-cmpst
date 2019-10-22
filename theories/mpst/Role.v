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

Module Rvar := MkLnVar avar.
Notation rvar := Rvar.t.
Canonical rvar_eqType := Rvar.eqType.


Parameter mty : eqType.
Parameter lbl : choiceType.

Notation role_set := {fset role}.
Notation lbl_alt  := {fset lbl}.

Parameter mty_lbl : mty -> lbl_alt.
Parameter lbl_mty : lbl_alt -> mty.
Parameter lbl_mty_iso : forall l t, (lbl_mty l == t) = (l == mty_lbl t).
