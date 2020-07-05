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

Create HintDb mpst.

Lemma dual_actK a : dual_act (dual_act a) = a.
Proof. by case: a. Qed.
Hint Rewrite dual_actK : mpst.

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
| mk_act (a : l_act) (p : role) (q : role) (l : lbl) (t : mty).

(* a trace is simply a stream of actions *)
CoInductive trace (act : Type) :=
| tr_end : trace act
| tr_next : act -> trace act -> trace act.

CoFixpoint trace_map {A B : Type} (f : A -> B) (trc : trace A) : trace B :=
  match trc with
  | tr_end => tr_end _
  | tr_next a trc => tr_next (f a) (trace_map f trc)
  end
.

Definition subject A := let: mk_act a p q _ _ := A in p.
Definition object A := let: mk_act a p q _ _ := A in q.
Definition act_ty A := let: mk_act a _ _ _ _ := A in a.

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
Hint Rewrite fsetUs_list : mpst.

Lemma fsetUs_fset0 (A : choiceType) (Ks : seq {fset A}) :
  fsetUs Ks == fset0 <-> (forall K, member K Ks -> K == fset0).
Proof.
  elim: Ks=>// K Ks Ih/=; rewrite fsetUs_list -(rwP andP) Ih {Ih}; split.
  - by move=>[/eqP-> H] K' [/eqP|/H].
  - by move=> H; split; [apply: H; left| move=>K' K'Ks; apply: H; right].
Qed.

Lemma fsetUs_cons (K : choiceType) (x : K) s L :
  x \in fsetUs (s :: L) = (x \in s) || (x \in fsetUs L).
Proof.
  rewrite /fsetUs/=.
  elim: L fset0 => [s'|s' L Ih s'']/=; first (by rewrite in_fsetU orbC).
  by rewrite fsetUC fsetUA Ih fsetUC.
Qed.
Hint Rewrite fsetUs_cons : mpst.


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
  - elim: L H M=>// y L /=Ih H [->|H'].
    + by apply: H; left.
    + by apply: Ih=>// z M; apply: H; right.
Qed.
Hint Rewrite member_map : mpst.

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

Notation "K .lbl" := (K.1) (at level 2,
                            left associativity,
                            format "K .lbl") : mpst_scope.
Notation "K .mty" := (K.2.1) (at level 2,
                              left associativity,
                              format "K .mty") : mpst_scope.
Notation "K .cnt" := (K.2.2) (at level 2,
                              left associativity,
                              format "K .cnt") : mpst_scope.

Reserved Notation "x '/->' y" (at level 99, right associativity, y at level 200).
Notation "x '/->' y" := (x -> option y) : mpst_scope.

Open Scope mpst_scope.
Definition empty A : (lbl /-> A) := fun=> None.
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

(*Definition same_dom T (C C' : lbl /-> mty * T) :=
  forall L Ty, (exists G, C L = Some (Ty, G)) <-> (exists G', C' L = Some (Ty, G')).*)

Definition same_dom T T' (C : lbl /-> mty * T) (C' : lbl /-> mty * T') :=
  forall L Ty, (exists G, C L = Some (Ty, G)) <-> (exists G', C' L = Some (Ty, G')).

Lemma same_dom_refl A (C1 : lbl /-> mty * A) : same_dom C1 C1.
Proof. by []. Qed.

Lemma same_dom_sym A B (C1 : lbl /-> mty * A) (C2 : lbl /-> mty * B) :
  same_dom C1 C2 <-> same_dom C2 C1.
Proof. by split=>H l Ty; move: (H l Ty)=>->. Qed.

Lemma same_dom_trans A B C
      (C1 : lbl /-> mty * A) (C2 : lbl /-> mty * B) (C3 : lbl /-> mty * C) :
  same_dom C1 C2 -> same_dom C2 C3 -> same_dom C1 C3.
  Proof. by move=>H0 H1 l Ty; move: (H0 l Ty) (H1 l Ty)=>->. Qed.

Lemma same_dom_extend T1 T2 l Ty G1 G2
  (C1 : lbl /-> mty * T1) (C2 : lbl /-> mty * T2):
  same_dom C1 C2 ->
  same_dom (extend l (Ty, G1) C1) (extend l (Ty, G2) C2).
Proof.
rewrite /extend /same_dom; move=> hp l0 Ty0; case: ifP =>//=; move=> eq.
by split; elim; move=> GG [eqTy eqG]; rewrite eqTy; [exists G2 | exists G1].
Qed.

Lemma same_dom_extend_some_l T1 T2 l Ty G1 G2
  (C1 : lbl /-> mty * T1) (C2 : lbl /-> mty * T2):
  same_dom C1 C2 -> C1 l = Some (Ty, G1) ->
  same_dom C1 (extend l (Ty, G2) C2).
Proof.
rewrite /extend /same_dom; move=> hp eq l0 Ty0.
case: ifP =>//=; rewrite -(rwP eqP); move=> eql; rewrite -eql.
split; [| by elim; move=> GG [eq1 eq2]; rewrite -eq1; exists G1].
by elim=> GG; rewrite eq; move=> [eq1 eq2]; exists G2; rewrite eq1.
Qed.

Definition same_dom_const T1 T2 (C: lbl /-> mty * T1) (t2 : T2) L :=
match C L with
  | None => None
  | Some (Ty,t1) => Some (Ty,t2)
end.

Lemma same_dom_const_same_dom T1 T2 (C: lbl /-> mty * T1) (t : T2):
  same_dom C (same_dom_const C t).
Proof.
rewrite /same_dom /same_dom_const; move=> L Ty; split.
+ by elim=> G hp; exists t; rewrite hp.
+ elim=> G; case: (C L) => //=; move=> a.
  by case: a => Tyy t1 [eq1 eq2]; exists t1; rewrite eq1.
Qed.

Lemma same_dom_const_some T1 T2 (C: lbl /-> mty * T1) (t:T2) L Ty t':
  same_dom_const C t L = Some (Ty, t') -> t' = t.
Proof.
rewrite /same_dom_const; case: (C L) => //=; move=> a.
case: a=> Tyy _ [] =>//=.
Qed.

Lemma dom T T' (C0 : lbl /-> mty * T) (C1 : lbl /-> mty * T')
      (DOM : same_dom C0 C1)
  : forall l Ty G, C0 l = Some (Ty, G) -> exists G', C1 l = Some (Ty, G').
Proof. by move=> l Ty; move: (DOM l Ty)=>[/(_ (ex_intro _ _ _))-H _]. Qed.

Lemma dom' T T' (C0 : lbl /-> mty * T) (C1 : lbl /-> mty * T')
      (DOM : same_dom C0 C1)
  : forall l Ty G, C1 l = Some (Ty, G) -> exists G', C0 l = Some (Ty, G').
Proof. by move=> l Ty; move: (DOM l Ty)=>[_ /(_ (ex_intro _ _ _))-H]. Qed.


Lemma dom_none A B (C0 : lbl /-> mty * A) (C1 : lbl /-> mty * B)
  : same_dom C0 C1 -> forall l, C0 l = None -> C1 l = None.
Proof.
  move=>DOM l Cl; case C1l: (C1 l)=>[[Ty] b|]//.
    by move: (dom' DOM C1l)=>[G0]; rewrite Cl.
Qed.

Lemma dom_none' A B (C0 : lbl /-> mty * A) (C1 : lbl /-> mty * B)
  : same_dom C0 C1 -> forall l, C1 l = None -> C0 l = None.
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

Definition P_all A (P : A -> Prop) (F : lbl /-> mty * A) :=
  forall l Ty a, F l = Some (Ty, a) -> P a.

Definition R_all T T' (R : T -> T' -> Prop)
           (C : lbl /-> mty * T) (C' : lbl /-> mty * T'):=
    forall L Ty G G',
    C L = Some (Ty, G) -> C' L = Some (Ty, G') -> R G G'.


Close Scope mpst_scope.
