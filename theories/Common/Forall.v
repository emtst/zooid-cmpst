From mathcomp.ssreflect Require Import all_ssreflect seq.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Fixpoint Forall A (P : A -> Prop) (l : seq A) :=
  match l with
  | [::] => True
  | h :: t => P h /\ Forall P t
  end.

Fixpoint Forall2 A (P : A -> A -> Prop) (l1 l2 : seq A) :=
  match l1, l2 with
  | [::], [::] => True
  | h1 :: t1, h2 :: t2 => P h1 h2 /\ Forall2 P t1 t2
  | _, _ => False
  end.

Lemma Fa_cat A (P : A -> Prop) (l1 l2 : seq A) :
  Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
Proof.
  elim: l1=>/=; first (by split=>[H|[_ H]];[split|]).
  by move=> a l1 Ih; rewrite Ih and_assoc.
Qed.

Lemma Fa_rev A (P : A -> Prop) (l : seq A) : Forall P l <-> Forall P (rev l).
Proof.
  elim: l=>//a l Ih/=.
  rewrite -[a::l]/([::a] ++ l) rev_cat Fa_cat/= -and_assoc.
  have H Q : Q <-> Q /\ True by split=>//[[]].
  by rewrite -H Ih and_comm.
Qed.

Lemma Fa_map A B (P : A -> Prop) (f : B -> A) (l : seq B) :
  Forall P [seq f x | x <- l] <-> Forall (fun x => P (f x)) l.
Proof. by elim l=>//a {l}l Ih/=; rewrite Ih. Qed.

Lemma Fa_rw A (P : A -> Prop) (Q : A -> Prop) (l : seq A) :
  (forall X, P X -> Q X) ->
  Forall (fun X => P X) l ->
  Forall (fun X => Q X) l.
Proof. by move=> PQ;elim l=>///=h t Ih [/PQ-Qh /Ih-Qt]; split. Qed.

Lemma Fa_conj A (P1 P2 : A -> Prop) l :
  Forall P1 l -> Forall P2 l -> Forall (fun x => P1 x /\ P2 x) l.
Proof.
  by elim l=>///= h t=> Ih [Ph1 Pt1] [Ph2 Pt2]; do ! (split=>//); apply: Ih.
Qed.

Lemma Fa_lift A B (P : A -> B -> Prop) l :
  Forall (fun X => forall y, P X y) l -> forall y, Forall (P^~y) l.
Proof. by move=> F y; move: F; apply: Fa_rw => X PX. Qed.

Lemma Fa_app A (P : A -> Prop) (Q : A -> Prop) (l : seq A) :
  Forall (fun X => (P X -> Q X) /\ P X) l ->
  Forall (fun X => Q X) l.
Proof. by elim l=>///=h t Ih [[PQh /PQh-Qh] /Ih-PQt]; split. Qed.

Lemma Fa_map_eq A B (f g : A -> B) l :
  Forall (fun a => f a = g a) l -> [seq f a | a <- l] = [seq g a | a <- l].
Proof. by elim l=>// h t/= Ih [-> /Ih->]. Qed.

Lemma forallP T P (f : T -> bool) (l : seq T) :
  (forall x, reflect (P x) (f x)) -> reflect (Forall P l) (all f l).
Proof.
  move=> PP; elim: l=>/=.
  + by apply: ReflectT.
  + move=> h t Ih; case: PP.
    - case: Ih => Pt Ph.
      * by apply: ReflectT; split.
      * by apply: ReflectF =>[[_]].
    - by move=> Fh{Ih}; apply: ReflectF=>[[Ph _]].
Qed.

Lemma forallbP T (f : T -> bool) l :
  reflect (Forall f l) (all f l).
Proof. by apply: forallP=>x; apply: idP. Qed.
