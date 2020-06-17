From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Forall.

Definition maximum := foldr maxn 0.

Lemma in_maximum_leq v l: v \in l -> v <= maximum l.
Proof.
  elim: l=>//v' l Ih; rewrite in_cons=>/orP-[/eqP<-|]/=.
  + by apply: leq_maxl.
  + by move=>/Ih{Ih}; move: (maximum l) => k {l}; rewrite leq_max orbC=>->.
Qed.

(*
Lemma maximum_in l r : maximum l < maximum r ->
                       exists v, v \in r /\ forall v', v' \in l -> v' < v.
  elim: r l =>/=// rh rt Ih l.
  rewrite leq_max=>/orP[H|H].
  - exists rh; rewrite in_cons eq_refl; split=>// v' /in_maximum_leq-H'.
    by (apply: leq_ltn_trans H' H).
  - move: (Ih l H) =>{Ih} [v [v_rt Ih]].
    by exists v; rewrite in_cons orbC v_rt; split.
Qed.
*)

Module Type Atom.
  Parameter t : choiceType.
  Parameter mk_atom : nat -> t.
  Parameter fresh : {fset t} -> t.
  Parameter freshK : forall s, fresh s \notin s.
  Lemma is_fresh s1 s2 : fsubset s1 s2 -> fresh s2 \notin s1.
  Proof.
    move=> /eqP<-; rewrite in_fsetI negb_and; apply/orP; right=>{s1}.
    by apply: freshK.
  Qed.
End Atom.

Module def_atom : Atom.
  Definition t := nat_choiceType.
  Definition mk_atom (x : nat) : t := x.
  Definition fresh (s : {fset t}) : t := (maximum s).+1.

  Lemma freshK s : fresh s \notin s.
  Proof. by apply: contraT; rewrite negbK => /in_maximum_leq; rewrite ltnn. Qed.

  Lemma is_fresh s1 s2 : fsubset s1 s2 -> fresh s2 \notin s1.
  Proof.
    move=> /eqP<-; rewrite in_fsetI negb_and; apply/orP; right=>{s1}.
    by apply: freshK.
  Qed.
End def_atom.

(* Generative atom interface to create new kinds of atoms *)
Module NewAtom (m : Atom) : Atom.
  Definition t := m.t.
  Definition mk_atom := m.mk_atom.
  Definition fresh := m.fresh.
  Definition is_fresh := m.is_fresh.
  Definition freshK := m.freshK.
End NewAtom.
