From mathcomp.ssreflect Require Import all_ssreflect seq.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.Forall.

Notation member := List.In.

Lemma forall_member A P (l : seq A) :
  Forall P l <-> forall x, member x l -> P x.
Proof.
  elim l=>// x {l}l [IhL IhR] /=; split.
  + by move=>[Px /IhL-Pl] x0 [<-|/Pl].
  + move=> H; split.
    - by apply: H; left.
    - by apply: IhR=>x0 x0_l; apply: H; right.
Qed.

Lemma memberP (A : eqType) (x : A) l : reflect (member x l) (x \in l).
Proof.
  elim l; first by apply: ReflectF.
  move=> a {l}l Ih/=; rewrite in_cons; case: eqP=>[->|x_aF].
  + by apply: ReflectT; left.
  + case: Ih=>[x_l|x_lF].
    - by apply: ReflectT; right.
    - by apply: ReflectF=>[[/esym-x_a|x_l]].
Qed.

Lemma cat_eq_nil (A : eqType) (K1 K2 : seq A)
  : K1 ++ K2 == [::] <-> K1 == [::] /\ K2 == [::].
Proof.
  split.
  - by move=>/eqP; case: K1=>//=->.
  - by move=>[/eqP->/eqP->].
Qed.

Lemma flatten_eq_nil (A : eqType) (Ks : seq (seq A)) :
  flatten Ks == [::] <-> forall K, member K Ks -> K == [::].
Proof.
  split.
  - by elim: Ks=>//= K Ks Ih /cat_eq_nil-[/eqP-> /Ih-H {}K [->|/H]].
  - elim: Ks=>//= K Ks Ih H; apply/cat_eq_nil;split; first by apply/H; left.
      by apply/Ih=>K' H'; apply/H; right.
Qed.

Lemma member_map A B (P : B -> Prop) (f : A -> B) L :
  (forall x, member x [seq f x | x <- L] -> P x) <->
  (forall x, member x L -> P (f x)).
Proof.
  split=>H x M.
  - apply: H; elim: L M=>// y L Ih [<-|]; first by left.
    by rewrite -/(member _ _) => /Ih-H /=; right.
  - elim: L H M=>// y L /=Ih H [<-|H'].
    + by apply: H; left.
    + by apply: Ih=>// z M; apply: H; right.
Qed.
Hint Rewrite member_map : mpst.
