From mathcomp.ssreflect Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition role:=nat.
Definition lbl := nat.

(* Supported messages *)
Inductive mty : Type :=
| T_nat : mty
| T_bool : mty
| T_unit : mty
| T_sum : mty -> mty -> mty
| T_prod : mty -> mty -> mty
(* | T_seq : mty -> mty *)
.

Fixpoint mty_eq (m1 m2 : mty) : bool :=
  match m1, m2 with
  | T_nat, T_nat => true
  | T_bool, T_bool => true
  | T_unit, T_unit => true
  | T_sum l1 r1, T_sum l2 r2 => mty_eq l1 l2 && mty_eq r1 r2
  | T_prod l1 r1, T_prod l2 r2 => mty_eq l1 l2 && mty_eq r1 r2
  (* | T_seq t1, T_seq t2 => mty_eq t1 t2 *)
  | _, _ => false
  end.

Lemma mty_eqP t1 t2 : reflect (t1 = t2) (mty_eq t1 t2).
Proof.
  elim: t1 t2=>[|||l1 Ihl r1 Ihr|l1 Ihl r1 Ihr] [|||l2 r2|l2 r2]/=; try by constructor.
  - case: Ihl=>[<-|E]/=; last by constructor=>[][].
    case: Ihr=>[<-|E]/=; last by constructor=>[][].
    by constructor.
  - case: Ihl=>[<-|E]/=; last by constructor=>[][].
    case: Ihr=>[<-|E]/=; last by constructor=>[][].
    by constructor.
Qed.

Definition mty_eqMixin := EqMixin mty_eqP.
Canonical mty_eqType := Eval hnf in EqType mty mty_eqMixin.

Fixpoint coq_ty m :=
  match m with
  | T_nat => nat
  | T_bool => bool
  | T_unit => unit
  | T_sum l r => coq_ty l + coq_ty r
  | T_prod l r => coq_ty l * coq_ty r
  (* | T_seq l => seq (coq_ty l) *)
  end%type.

Fixpoint eq_coq_ty' {T} : coq_ty T -> coq_ty T -> bool
  := match T with
     | T_nat => fun n m => n == m
     | T_bool => fun n m => n == m
     | T_unit => fun n m => n == m
     | T_sum Tl Tr =>
       fun n m =>
         match n, m with
         | inl x, inl y => eq_coq_ty' x y
         | inr x, inr y => eq_coq_ty' x y
         | _, _ => false
         end
     | T_prod Tl Tr =>
       fun n m =>
         match n, m with
         | (x1, x2), (y1, y2) => eq_coq_ty' x1 y1 && eq_coq_ty' x2 y2
         end
     end.

Lemma coq_ty_eqP' {T} : Equality.axiom (@eq_coq_ty' T).
Proof.
  elim: T=>[|||Tl Ihl Tr Ihr|Tl Ihl Tr Ihr]/=x y; try by apply/eqP.
  - case: x=>x; case: y=>y/=; try by constructor.
    + by case: Ihl=>[<-|E]; constructor=>//[][].
    + by case: Ihr=>[<-|E]; constructor=>//[][].
  - case: x=>[x1 x2]; case: y=>[y1 y2]/=.
    case: Ihl=>[<-|E]/=; try by constructor=>[][].
    case: Ihr=>[<-|E]/=; try by constructor=>[][].
    by constructor.
Qed.

Definition coq_ty_eqMixin {T} := EqMixin (@coq_ty_eqP' T).
Canonical coq_ty_eqType {T} := Eval hnf in EqType (coq_ty T) coq_ty_eqMixin.

Definition eq_coq_ty {T1 T2} : coq_ty T1 -> coq_ty T2 -> bool :=
  match @eqP _ T1 T2 with
  | ReflectT H =>
    match H with
    | erefl => eq_coq_ty'
    end
  | ReflectF _ =>
    fun _ _ => false
  end.
