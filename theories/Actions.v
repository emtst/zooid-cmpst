From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
From Paco Require Import paco2.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.AtomSets.
Require Import MPST.Forall.

Inductive l_act := l_send | l_recv.

Definition dual_act a :=
  match a with
  | l_send => l_recv
  | l_recv => l_send
  end.

Lemma dual_actK a : dual_act (dual_act a) = a.
Proof. by case: a. Qed.

Definition eq_lact a b :=
  match a, b with
  | l_send, l_send
  | l_recv, l_recv => true
  | _, _ => false
  end.

Lemma lact_eqP : Equality.axiom eq_lact.
Proof. by rewrite /Equality.axiom => [[] []/=]; constructor. Qed.

Definition lact_eqMixin := EqMixin lact_eqP.
Canonical lact_eqType := Eval hnf in EqType l_act lact_eqMixin.


Inductive act :=
| a_send (p : role) (q : role) (l : lbl) (t : mty)
| a_recv (p : role) (q : role) (l : lbl) (t : mty)
.

CoInductive trace :=
| tr_end : trace
| tr_next : act -> trace -> trace.

Definition subject a :=
  match a with
  | a_send p _ _ _ => p
  | a_recv _ q _ _ => q
  end.

Fixpoint lookup (E : eqType) A (p : E) (K : seq (E * A)) : option A :=
  match K with
  | [::] => None
  | h :: t => if h.1 == p then Some h.2 else lookup p t
  end.

Definition MsgQ := seq ((role * role) * seq (lbl * mty)).

Fixpoint enqueue (A : eqType) B (p : seq (A * seq B)) (x : A * B) :=
  match p with
  | [::] => [:: (x.1, [:: x.2])]
  | h :: t => if h.1 == x.1 then (h.1, h.2 ++ [:: x.2]) :: t
              else h :: enqueue t x
  end.

Fixpoint dequeue (A : eqType) B (p : seq (A * seq B)) (x : A)
  : option (B * seq (A * seq B)) :=
  match p with
  | [::] => None
  | h :: t => if h.1 == x then match h.2 with
                               | [::] => None
                               | f :: q => Some (f, (h.1, q) :: t)
                               end
              else match dequeue t x with
                   | None => None
                   | Some (e, t') => Some (e, h :: t')
                   end
  end.

Definition fsetUs (K : choiceType) : seq {fset K} -> {fset K}
  := foldl fsetU fset0.

Lemma notin_unions (X : choiceType) (x : X) (l : seq {fset X}) :
  (x \notin fsetUs l) <-> Forall (fun e => x \notin e) l.
Proof.
  rewrite /fsetUs Fa_rev -(revK l) foldl_rev revK; move: (rev l)=> {l}l.
  by elim: l => // a l Ih /=; rewrite fsetUC in_fsetU negb_or -(rwP andP) Ih.
Qed.

Lemma foldl_fsetU (A : choiceType) (K : {fset A}) Ks :
  foldl fsetU K Ks = (K `|` foldl fsetU fset0 Ks)%fset.
Proof.
  rewrite -[in LHS](fset0U K); elim: Ks fset0=>[K'|K' Ks Ih K'']/=.
  - by rewrite fsetUC.
  - move: (Ih (K'' `|` K')%fset)=>{Ih}<-.
    by rewrite -fsetUA [(K `|` K')%fset]fsetUC fsetUA.
Qed.

Lemma fsetUs_list (A : choiceType) (K : {fset A}) Ks :
  fsetUs (K :: Ks) == fset0 = (K == fset0) && (fsetUs Ks == fset0).
Proof.
  by rewrite /fsetUs/= fset0U foldl_fsetU fsetU_eq0.
Qed.

Lemma fsetUs_fset0 (A : choiceType) (Ks : seq {fset A}) :
  fsetUs Ks == fset0 <-> (forall K, member K Ks -> K == fset0).
Proof.
  elim: Ks=>// K Ks Ih/=; rewrite fsetUs_list -(rwP andP) Ih {Ih}; split.
  - by move=>[/eqP-[-> H]] K' [->//|/H].
  - by move=> H; split; [apply: H; left| move=>K' K'Ks; apply: H; right].
Qed.

Lemma fsetUs_cons (K : choiceType) (x : K) s L :
  x \in fsetUs (s :: L) = (x \in s) || (x \in fsetUs L).
Proof.
  rewrite /fsetUs/=.
  elim: L fset0 => [s'|s' L Ih s'']/=; first (by rewrite in_fsetU orbC).
  by rewrite fsetUC fsetUA Ih fsetUC.
Qed.


Lemma member_map A B (P : B -> Prop) (f : A -> B) L :
  (forall x, member x [seq f x | x <- L] -> P x) <->
  (forall x, member x L -> P (f x)).
Proof.
  split=>H x M.
  - apply: H; elim: L M=>// y L Ih [<-|]; first by left.
    by rewrite -/(member _ _) => /Ih-H /=; right.
  - elim: L H M=>// y L /=Ih H [->|H'].
    + by apply: H; left.
    + by apply: Ih=>// z M; apply: H; right.
Qed.

Lemma fsetUs_eq A (B : choiceType) (f g : A -> {fset B}) L :
  (forall x, member x L -> f x = g x) ->
  fsetUs [seq f x | x <- L] = fsetUs [seq g x | x <- L].
Proof.
  rewrite /fsetUs; elim: L {1 2}fset0 {1 3}fset0 (eq_refl (@fset0 B)).
  - by move=> Sl Sr /eqP->{Sr}/=.
  - move=> x L Ih S0 S1 /eqP-> H; apply/Ih; first by rewrite (H x _)//; left.
    by move=> y H'; apply/H; right.
Qed.

(* Declare Scope mpst_scope. *)

Definition alt (x : Type) := (lbl * (mty * x))%type.

Notation "K .lbl" := (K.1)   (at level 2, left associativity, format "K .lbl") : mpst_scope.
Notation "K .mty" := (K.2.1) (at level 2, left associativity, format "K .mty") : mpst_scope.
Notation "K .cnt" := (K.2.2) (at level 2, left associativity, format "K .cnt") : mpst_scope.

Reserved Notation "x '/->' y" (at level 99, right associativity, y at level 200).
Notation "x '/->' y" := (x -> option y) : mpst_scope.

Open Scope mpst_scope.
Definition empty A : (lbl /-> mty * A) := fun=> None.
Definition extend A (L : lbl) (X : A) f :=
  fun L' => if L == L' then Some X else f L'.

Definition same_dom T (C C' : lbl /-> mty * T) :=
  forall L Ty, (exists G, C L = Some (Ty, G)) <-> (exists G', C' L = Some (Ty, G')).

Definition R_all T T' (R : rel2 T (fun=>T'))
           (C : lbl /-> mty * T) (C' : lbl /-> mty * T'):=
  forall L Ty G G',
    C L = Some (Ty, G) -> C' L = Some (Ty, G') -> R G G'.
Close Scope mpst_scope.
