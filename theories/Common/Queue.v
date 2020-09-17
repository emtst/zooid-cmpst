From mathcomp.ssreflect Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.AtomSets.

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
