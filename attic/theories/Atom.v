(* Atoms for locally nameless *)

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq path.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module Type ATOM.

  Parameter atom : Set.
  Definition t := atom.

  (* atoms can be compared to booleans *)

  Parameter eq_atom : atom -> atom -> bool.
  Parameter eq_reflect : forall (a b : atom), ssrbool.reflect (a = b) (eq_atom a b).
  Parameter atom_eqMixin : Equality.mixin_of atom.
  Canonical atom_eqType := EqType atom atom_eqMixin.

  Parameter fresh : seq atom -> atom.

  Parameter fresh_not_in : forall l, (fresh l) \notin l.

  Parameter nat_of : atom -> nat.
End ATOM.

Module Atom : ATOM.

  (* begin hide *)
  Definition atom := nat.
  Definition t := atom.

  Definition eq_atom (a b : nat) : bool := ssrnat.eqn a b.

  Lemma eq_reflect a b :  ssrbool.reflect (a = b) (eq_atom a b).
  Proof. by apply: ssrnat.eqnP. Qed.

  Definition atom_eqMixin := EqMixin Atom.eq_reflect.
  Canonical atom_eqType := EqType atom atom_eqMixin.

  Fixpoint fresh' a (l : seq atom) :=
    match l with
    | [::] => a +1
    | x::xs => fresh' (maxn x a) xs
    end.

  Definition fresh l := fresh' 0 l.

  Lemma fresh_not_head a a' l : a <= a' -> fresh' a' l != a.
  Proof.
    elim: l a' => [|  a'' l IHl] a' Le_a_a'.
      by rewrite /fresh' neq_ltn addn1 ltnS orb_idl.
    by rewrite /fresh' maxnC; apply IHl; rewrite leq_max orb_idr.
  Qed.

  Lemma fresh_not_in l : fresh l \notin l.
  Proof.
    suff fresh'_not_in a : fresh' a l \notin l by apply fresh'_not_in.
    elim: l a =>  // a' l IHl a.
      by rewrite /fresh/fresh' in_cons Bool.negb_orb fresh_not_head ?(IHl (maxn a' a)) ?leq_maxl.
  Qed.

  Definition nat_of (x : atom) := x.
  (* end hide *)
End Atom.

(** We make [atom], [fresh], [fresh_not_in] and [atom_fresh_for_list] available
    without qualification. *)

Notation atom := Atom.atom.
Notation fresh := Atom.fresh.
Notation fresh_not_in := Atom.fresh_not_in.

Canonical atom_eqType := EqType Atom.atom Atom.atom_eqMixin.
