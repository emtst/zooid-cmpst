From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Atom.

(* FIXME: Should be a parameterised type Inductive lnvar t := ... *)
Module MkLnVar(M : Atom).
  Inductive t :=
  | fv (a : M.t)
  | bv (n : nat).

  Coercion bv : nat >-> t.
  (* Coercion fv : atom >-> t. *)

  Definition eq_var a b :=
    match a, b with
    | fv a1, fv a2 => a1 == a2
    | bv n1, bv n2 => n1 == n2
    | _, _ => false
    end.

  Lemma lnvar_eqP : Equality.axiom eq_var.
  Proof.
    by move=> x y; case: x; case: y=>/=l r; try (by apply: ReflectF);
             case: eqP => H; try rewrite H; constructor=>//[[]].
  Qed.

  Definition eqMixin := EqMixin lnvar_eqP.
  Canonical eqType := Eval hnf in EqType t eqMixin.

  Open Scope fset_scope.
  Definition fvar v : {fset M.t} :=
    match v with
    | fv a => [fset a]
    | _ => fset0
    end.
  Definition fbvar d v : {fset nat} :=
    match v with
    | bv n => if d <= n then [fset n - d] else fset0
    | _ => fset0
    end.
  Close Scope fset_scope.

  Definition open A (z : t -> A) (d : nat) (y : A) (x : t) :=
    match x with
    | fv _ => z x
    | bv n => if d == n then y else z x
    end.

  Definition close (v : M.t) (d : nat) (x : t) :=
    match x with
    | bv _ => x
    | fv a => if v == a then bv d else x
    end.

  Lemma open_close X d v :
    X \notin fvar v -> close X d (open id d (fv X) v) = v.
  Proof.
    case: v => [a|n _]/=.
    - by rewrite /close; case: ifP=>///eqP->; rewrite fset11.
    - by case: ifP=>///eqP->; rewrite /close eq_refl.
  Qed.

  (* XXX TOO  MUCH, SIMPLIFY *)
  Lemma fbvar0 n m v : (n \notin fbvar m v) = (n + m \notin fbvar 0 v).
  Proof.
    case: v=>///= d; case: ifP=>[|H]; rewrite subn0/=.
    - case: fset1P=>[->Le_m_d|].
      + by rewrite subnK //; case fset1P.
      + move =>/eqP-H1 H2; apply/esym/fset1P/eqP=>/=; move: H1.
        by apply: contraTT; rewrite !negbK=>/eqP<-; rewrite addnK.
    - apply/esym; move: H; rewrite (rwP negPf); apply: contraTT; rewrite !negbK.
      by move/fset1P=><-; apply: leq_addl.
  Qed.

  Lemma close_open X n m v :
    n \notin fbvar m v -> open id (n+m) (fv X) (close X (n+m) v) = v.
  Proof.
    rewrite fbvar0; move: (n+m)=>t{n m}.
    case: v =>[a _ | d/=]; rewrite /close.
    - by case:ifP; rewrite/open// eq_refl=>/eqP->.
    - by case: ifP =>///eqP->; rewrite subn0 fset11.
  Qed.

  Lemma open_fun A (f : t -> A) d w v : open f d (f w) v = f (open id d w v).
  Proof. by case: v=>//n; rewrite /open (fun_if f). Qed.
End MkLnVar.
