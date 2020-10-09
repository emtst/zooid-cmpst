From mathcomp.ssreflect Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.AtomSets.
Require Import MPST.Common.Member.

Definition alt (x : Type) := (lbl * (mty * x))%type.

Definition empty A : (lbl -> option A) := fun=> None.
Definition extend A (L : lbl) (X : A) f :=
  fun L' => if L == L' then Some X else f L'.

Fixpoint find_cont A (c : seq (lbl * A))
  : lbl -> option A
  := match c with
     | [::] => empty A
     | (k, v) :: c => extend k v (find_cont c)
     end.

Lemma find_member A (c : seq (lbl * (mty * A))) l Ty G :
  find_cont c l = Some (Ty, G) -> member (l, (Ty, G)) c.
Proof.
  elim: c=>//= [[k v]] ks Ih; rewrite /extend/=.
  case: ifP=>[/eqP->[->]|]//; first by left.
  by move=> _ /Ih-H; right.
Qed.

Lemma in_cons_tail (A : eqType) B (t : seq (A * B)) (x : A) k v :
  x <> k ->
  x \in [seq y.1 | y <- (k, v) :: t] ->
  x \in [seq y.1 | y <- t].
Proof. by rewrite /= in_cons=>/eqP/negPf->. Qed.

Fixpoint get_v B (ls : seq (lbl * B)) x
  : find_cont ls x -> B
  := match find_cont ls x as P return P -> B with
     | Some y => fun=> y
     | None => fun P => match not_false_is_true P with end
     end.


(*NMC: lemma needed now, but  maybe will not be anymore after we improve axioms*)
Lemma find_cont_map A B Ks l (a:A) (f: A-> B):
  find_cont Ks l = Some a -> find_cont (map (fun K=> (K.1, f K.2)) Ks) l = Some (f a).
Proof.
  elim: Ks=>//= [[k v]] ks Ih; rewrite /extend.
  by case: ifP; [move=> _ []=>->| move=> _].
Qed.

Definition same_dom T T'
           (C : lbl -> option (mty * T)) (C' : lbl -> option (mty * T'))
  := forall L Ty,
       (exists G, C L = Some (Ty, G)) <-> (exists G', C' L = Some (Ty, G')).

Lemma same_dom_refl A C1 : @same_dom A A C1 C1.
Proof. by []. Qed.

Lemma same_dom_sym A B C1 C2 : @same_dom A B C1 C2 <-> @same_dom B A C2 C1.
Proof. by split=>H l Ty; move: (H l Ty)=>->. Qed.

Lemma same_dom_trans A B C C1 C2 C3 :
  @same_dom A B C1 C2 -> @same_dom B C C2 C3 -> @same_dom A C C1 C3.
Proof. by move=>H0 H1 l Ty; move: (H0 l Ty) (H1 l Ty)=>->. Qed.

Lemma same_dom_extend T1 T2 l Ty G1 G2 C1 C2 :
  @same_dom T1 T2 C1 C2 ->
  @same_dom T1 T2 (extend l (Ty, G1) C1) (extend l (Ty, G2) C2).
Proof.
  rewrite /extend /same_dom; move=> hp l0 Ty0; case: ifP =>//=; move=> eq.
  by split; elim; move=> GG [eqTy eqG]; rewrite eqTy; [exists G2 | exists G1].
Qed.

Lemma same_dom_extend_some_l T1 T2 l Ty G1 G2 C1 C2 :
  @same_dom T1 T2 C1 C2 -> C1 l = Some (Ty, G1) ->
  @same_dom T1 T2 C1 (extend l (Ty, G2) C2).
Proof.
  rewrite /extend /same_dom; move=> hp eq l0 Ty0.
  case: ifP =>//=; rewrite -(rwP eqP); move=> eql; rewrite -eql.
  split; [| by elim; move=> GG [eq1 eq2]; rewrite -eq1; exists G1].
  by elim=> GG; rewrite eq; move=> [eq1 eq2]; exists G2; rewrite eq1.
Qed.

Definition same_dom_const T1 T2 (C: lbl -> option (mty * T1)) (t2 : T2) L :=
match C L with
  | None => None
  | Some (Ty,t1) => Some (Ty,t2)
end.

Lemma same_dom_const_same_dom A B C t : @same_dom A B C (same_dom_const C t).
Proof.
  rewrite /same_dom /same_dom_const; move=> L Ty; split.
  + by elim=> G hp; exists t; rewrite hp.
  + elim=> G; case: (C L) => //=; move=> a.
    by case: a => Tyy t1 [eq1 eq2]; exists t1; rewrite eq1.
Qed.

Lemma same_dom_const_some A B C t L Ty t':
  @same_dom_const A B C t L = Some (Ty, t') -> t' = t.
Proof.
  by rewrite /same_dom_const; case: (C L) => //=; move=> [Tyy _ []].
Qed.

Lemma dom T T' C0 C1 (DOM : @same_dom T T' C0 C1)
  : forall l Ty G, C0 l = Some (Ty, G) -> exists G', C1 l = Some (Ty, G').
Proof. by move=> l Ty; move: (DOM l Ty)=>[/(_ (ex_intro _ _ _))-H _]. Qed.

Lemma dom' T T' C0 C1 (DOM : @same_dom T T' C0 C1)
  : forall l Ty G, C1 l = Some (Ty, G) -> exists G', C0 l = Some (Ty, G').
Proof. by move=> l Ty; move: (DOM l Ty)=>[_ /(_ (ex_intro _ _ _))-H]. Qed.

Lemma dom_none A B C0 C1
  : @same_dom A B C0 C1 -> forall l, C0 l = None -> C1 l = None.
Proof.
  move=>DOM l Cl; case C1l: (C1 l)=>[[Ty] b|]//.
    by move: (dom' DOM C1l)=>[G0]; rewrite Cl.
Qed.

Lemma dom_none' A B C0 C1
  : @same_dom A B C0 C1 -> forall l, C1 l = None -> C0 l = None.
Proof. by rewrite same_dom_sym; apply/dom_none. Qed.

Lemma samedom_nilp T T'
      (C0 : seq (lbl * (mty * T))) (C1 : seq (lbl * (mty * T')))
  : same_dom (find_cont C0) (find_cont C1) -> nilp C1 -> nilp C0.
Proof.
  case: C0=>// [][l [Ty G]] C0; case: C1=>// /(_ l Ty)-[/(_ (ex_intro _ G _))].
  by move=>/=; rewrite /extend eq_refl=>/(_ erefl)=>[][]//.
Qed.

Lemma same_dom_eta A B C
      (f : lbl -> option (mty * A))
      (g : lbl -> option (mty * B)) (h : B -> C) :
  same_dom f g ->
  same_dom f (fun l => match g l with
                       | Some (Ty, x) => Some (Ty, h x)
                       | None => None
                       end).
Proof.
  move=> DOM l T; case EQ: (f l)=>[[T' G']|];
    last by move: (dom_none DOM EQ)=>->; split=>[][].
  by move: (dom DOM EQ)=>[b->]; split=>[][x][<- _];
       [exists (h b)|exists G'].
Qed.

Definition P_all A (P : A -> Prop) (F : lbl -> option (mty * A)) :=
  forall l Ty a, F l = Some (Ty, a) -> P a.

Definition R_all T T' (R : T -> T' -> Prop)
           (C : lbl -> option (mty * T)) (C' : lbl -> option (mty * T')) :=
    forall L Ty G G',
    C L = Some (Ty, G) -> C' L = Some (Ty, G') -> R G G'.

(*NMC: lemma needed now, but  maybe will not be anymore after we improve axioms*)
Lemma find_cont_map_dom A B Ks (f: A-> B):
  same_dom (find_cont Ks) ( find_cont ( map ( fun K=> (K.1,(K.2.1,f K.2.2)) ) Ks ) ).
Proof.
  elim: Ks=>//=.
  + by  move=> l Ty; split;move => []G.
  + by move=> [l [Ty a]] Ks=> Ih //=; apply: (same_dom_extend ).
Qed.
