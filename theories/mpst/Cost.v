From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Global.

Section RecBound.
Inductive grec_b := inf | ubnd (n : nat).
Notation "\omega" := (inf).
End RecBound.

Section CostGT.
  Import Gvar.

  Inductive cg_ty : Type :=
  | cg_end : cg_ty
  | cg_var : gvar -> cg_ty
  | cg_rec : grec_b -> cg_ty -> cg_ty
  | cg_msg : nat*nat -> cg_ty -> cg_ty
  | cg_brn : nat*nat -> seq cg_ty -> cg_ty.

End CostGT.

(*
G = fix X. p -> q fix Y . { q -> r X | q -> p. Y }

=>

G1 X = fix k Y. { q -> r . X
                | q -> p. Y } ~ [p -> C1 | q -> C2] && [q < r] && [q < p]

G = fix k X. p -> q . (G1 (q -> r . X))
        ~ [p -> C1' + C1 + C2 | q -> C ]
&& [ p < q ] && [q < io(G1 end)] && [io (G1 end) < r p]


{G1} < p
q < {G1}
p < q

*)

Section Throughput.

  Fixpoint is_cycle (s : seq nat) : bool :=
    match s with
    | [::] => false
    | h :: t => (h \in t) || is_cycle t
    end.

  Record Path := mkPath { nodes : seq nat;
                          p_cycle : bool }.

  Definition add_step (n : nat) (l : Path) :=
    if (n \in nodes l)
    then if p_cycle l then l
         else mkPath (n :: nodes l) true
    else mkPath (n :: nodes l) (p_cycle l).

  Fixpoint extend (e : nat * nat) (ps : seq Path) :=
    map (add_step e.2) (filter (fun x => ohead (nodes x) == Some e.1) ps).

  Fixpoint add_paths g ps :=
    match g with
    | [::] => [::]
    | e :: es => extend e ps ++ add_paths es ps
    end.

  Fixpoint all_paths n g ps :=
    match n with
    | O => ps
    | S m => all_paths m g (add_paths g ps)
    end.

  Definition s_path (x : nat*nat) := mkPath [:: x.2; x.1] (x.2 == x.1).

  Fixpoint paths g :=
    all_paths (length g) g (map s_path g).

  Fixpoint sub_cycle (l1 l2 : seq nat * seq nat) :=
    all (fun x => x \in l2.1) l1.1 &&
        all (fun x => x \in l2.2) l1.2.

  Fixpoint take_until (h : nat) cy t :=
    match t with
    | x::xs => if (h == x) && (x \notin xs) then (t, h::cy)
               else take_until h (x::cy) xs
    | [::] => ([::], cy)
    end.

  Fixpoint take_cycle deps (l : seq nat) :=
    match l with
    | h :: t =>
      if (h \in t) && (~~ is_cycle t) then
        match take_until h [::] t with
        | (deps', cy) => (filter (fun x => x \notin cy) (undup (deps ++ deps')), undup cy)
        end
      else take_cycle (h::deps) t
    | [::] => ([::], [::])
    end.

  Fixpoint insert_subcycle (c : seq nat * seq nat) cs :=
    match cs with
    | [::] => [:: c]
    | h::t => if all (fun x => x \in h.2) c.2
              then let ndeps := h.1 ++ c.1 in
                   (filter (fun x => x \notin h.2) (undup ndeps), h.2) :: t
              else if all (fun x => x \in c.2) h.2
                   then let ndeps := h.1 ++ c.1 in
                        (filter (fun x => x \notin c.2) (undup ndeps), c.2) :: t
                   else h :: insert_subcycle c t
    end.

  Fixpoint filter_subcycles cs gs :=
    match gs with
    | h :: t => if p_cycle h
                then filter_subcycles (insert_subcycle (take_cycle [::] (nodes h)) cs) t
                else filter_subcycles cs t
    | [::] => cs
    end.

  Fixpoint map_filter A B (f : A -> option B) (x : seq A) : seq B :=
    match x with
    | [::] => [::]
    | h::t => match f h with
              | Some y => y :: map_filter f t
              | None => map_filter f t
              end
    end.

  Definition cycles g :=
    filter_subcycles [::] (paths g).

  Eval compute in paths [:: (2,3); (3,2); (2,1); (1,0); (0,2)].
  Eval compute in paths [:: (2,3); (3,2); (2,1); (1,0); (0,2); (3, 4); (4, 5); (5, 6); (6, 3)].
  Eval compute in
                 (paths [:: (2,3); (3,2); (2,1); (1,0); (0,2); (3, 4); (4, 5); (5, 6); (6, 3)]).
  Eval compute in cycles [:: (2,3); (3,2); (2,1); (1,0); (0,2); (3, 4); (4, 5); (5, 6); (6, 3)].
  Eval compute in cycles [:: (1,2); (2,3); (2, 1); (3, 1)].
  Eval compute in cycles [:: (1,2); (1,3); (1, 4); (2, 1); (3, 1); (4,1)].
  Eval compute in cycles [:: (1,2); (2,3); (3, 4); (4, 1); (5,6);(6,5)].
  Eval compute in paths [:: (1,2); (2,3); (3, 4); (4, 1); (5,6);(6,5)].
  Eval compute in cycles [:: (1,2); (2,3); (3, 4); (4, 1); (5,6);(6,5); (2,6)].

End Throughput.

(* Ex1:
Cost = C^omega (C^r(G)

mu X. 0 -> 1. 1 -> 0. end

C^r =>

0 -> 1
   [ 0 -> ts
   [ 1 -> tr + c1 ]

1 -> 0
   [ 0 -> ts + tr + c0
     1 -> ts + tr + c1 ]

0 -> 1
   [ 0 -> ts
   | 1 -> ts + tr + c0 + tr + c1 ]
1 -> 0
   [ 0 -> ts + ts + tr + c1 + tr + c0
     1 -> ts + tr + c0 + tr + c1 + ts
   ]
*)

(* Ex2:
Cost = C^omega (C^r(G)

mu X. 0 -> 1. 1 -> 0. 1 -> 2. end

C^r =>

0 --- ts + tr + c0.
1 --- tr + ts + ts + c1.
2 --- tr + c2.

C^omega (use 2-unfolding)
0 -> 1. G
  0 --- ts
  1 --- ts + tr + c0 + tr + c1  [1 < 0] G
  2 --- 0

1 -> 0 . G
  0 --- ts + tr + 2ts + c1 + tr + c0   [0 < 1] G
  1 --- ts + tr + c0 + tr + c1 + ts
  2 --- 0

1 -> 2 . G
  0 --- ts + tr + 2ts + c1 + tr + c0
  1 --- ts + tr + c0 + tr + c1 + ts + ts
  2 --- max(ts + tr + c0 + tr + c1 + ts + ts, tr + c2)    [ ~~ 2 < 1 ] G
*)

(* Ex3:

mu X. 0 -> 1. 1 -> 0. 1 -> 2. 2 -> 1. X

C^r |

C0 --- ts + tr + c0
C1 --- tr + c1 + ts + ts + tr + c1'
C2 --- tr + c2 + ts

C^o |

0 -> 1. 1 -> 0. 1 -> 2. 2 -> 1.    ||||  0 -> 1. 1 -> 0. 1 -> 2. 2 -> 1

0 --- max(C0, max (C0, C1 + C2)      [1 < 0] /// [0 < 1 < 2 < 1]
1 --- max(C0, C2) + C1                  [0 < 1 ] && [2 < 1 ] /// [ 1 < 2 ]
2 --- C1 + max(C2, C0)                  [1 < 2 ] /// [0 < 1 ] && [ 2 < 1]

[0, 1, 0]

[1, 0]

[1, 2, 1]

*)

(* Ex4:

mu X. 0 -> 1. 1 -> 0. 1 -> 2. X

C^r |

C0 --- ts + tr + c0
C1 --- tr + c1 + ts + ts
C2 --- tr + c2 + ts

C^o |

0 -> 1. 1 -> 0. 1 -> 2     ||||  0 -> 1. 1 -> 0. 1 -> 2

0 ---  [ 1 < 0 < 1 ] C1 + C0  max (C0, C1 + C0)
1 ---  [ 0 < 1 < 0 ] C0 + C1  max (C1, C0 + C1)
2 ---  max (C2, C0 + C1)

*)

End CostGT.
