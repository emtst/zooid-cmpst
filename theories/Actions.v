From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Role.

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

Definition MsgQ := seq ((role * role) * seq (lbl + mty)).

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

(* Declare Scope mpst_scope. *)

Notation "K .lbl" := (K.1)   (at level 2, left associativity, format "K .lbl") : mpst_scope.
Notation "K .mty" := (K.2.1) (at level 2, left associativity, format "K .mty") : mpst_scope.
Notation "K .cnt" := (K.2.2) (at level 2, left associativity, format "K .cnt") : mpst_scope.
