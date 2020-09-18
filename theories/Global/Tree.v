From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.

CoInductive rg_ty :=
| rg_end
| rg_msg (FROM TO : role)
         (CONT : lbl -> option (mty * rg_ty)).

Unset Elimination Schemes.
Inductive ig_ty :=
| ig_end (CONT : rg_ty)
| ig_msg (ST : option lbl)
         (FROM TO : role)
         (CONT : lbl -> option (mty * ig_ty)).
Set Elimination Schemes.

Definition P_option A (P : A -> Type) (C : option A) : Type :=
  match C with
  | Some X => P X
  | None => True
  end.

Definition P_prod A B (P : B -> Type) (C : A * B) : Type :=
  match C with
  | (X, Y)=> P Y
  end.

Lemma ig_ty_ind'
      (P : ig_ty -> Prop)
      (P_end : forall CONT, P (ig_end CONT))
      (P_msg : (forall ST FROM TO CONT,
                   (forall L, P_option (P_prod P) (CONT L)) ->
                   P (ig_msg ST FROM TO CONT)))
  : forall G, P G.
Proof.
  fix Ih 1; case.
  - by apply: P_end.
  - move=> ST F T C; apply: P_msg => L.
    case: (C L)=>[[Ty G]|].
    + by rewrite /P_option/P_prod; apply/Ih.
    + by rewrite /P_option.
Qed.

Lemma ig_ty_ind
      (P : ig_ty -> Prop)
      (P_end : forall CONT, P (ig_end CONT))
      (P_msg : (forall ST FROM TO CONT,
                   (forall L Ty G, CONT L = Some (Ty, G) -> P G) ->
                   P (ig_msg ST FROM TO CONT)))
  : forall G, P G.
Proof.
  elim/ig_ty_ind'=>// ST FROM TO CONT Ih.
  apply/P_msg => L Ty G; move: (Ih L); case: (CONT L) =>[[Ty' G']|]//=.
  by move=> P_G' [_ <-].
Qed.

Lemma ig_ty_rect'
      (P : ig_ty -> Type)
      (P_end : forall CONT, P (ig_end CONT))
      (P_msg : (forall ST FROM TO CONT,
                   (forall L, P_option (P_prod P) (CONT L)) ->
                   P (ig_msg ST FROM TO CONT)))
  : forall G, P G.
Proof.
  fix Ih 1; case.
  - by apply: P_end.
  - move=> ST F T C; apply: P_msg => L.
    case: (C L)=>[[Ty G]|].
    + by rewrite /P_option/P_prod; apply/Ih.
    + by rewrite /P_option.
Qed.

Lemma ig_ty_rect
      (P : ig_ty -> Type)
      (P_end : forall CONT, P (ig_end CONT))
      (P_msg : (forall ST FROM TO CONT,
                   (forall L Ty G, CONT L = Some (Ty, G) -> P G) ->
                   P (ig_msg ST FROM TO CONT)))
  : forall G, P G.
Proof.
  elim/ig_ty_rect'=>// ST FROM TO CONT Ih.
  apply/P_msg => L Ty G; move: (Ih L); case: (CONT L) =>[[Ty' G']|]//=.
  by move=> P_G' [_ <-].
Qed.

Inductive part_of: role -> rg_ty -> Prop :=
  | pof_from F T C: part_of F (rg_msg F T C)
  | pof_to F T C: part_of T (rg_msg F T C)
  | pof_cont p F T C L G Ty: C L = Some (Ty, G)
    -> part_of p G -> part_of p (rg_msg F T C).

Inductive part_of_all: role -> rg_ty -> Prop :=
  | pall_from F T C: part_of_all F (rg_msg F T C)
  | pall_to F T C: part_of_all T (rg_msg F T C)
  | pall_cont p F T C :
      P_all (part_of_all p) C -> part_of_all p (rg_msg F T C).

(* Needed to build the next global type in a step  *)
Inductive part_of_allT: role -> rg_ty -> Type :=
  | pallT_from F T C: part_of_allT F (rg_msg F T C)
  | pallT_to F T C: part_of_allT T (rg_msg F T C)
  | pallT_cont p F T C :
      (forall l Ty G, C l = Some (Ty, G) -> part_of_allT p G) ->
      part_of_allT p (rg_msg F T C).

Inductive iPart_of: role -> ig_ty -> Prop :=
  | ipof_end p cG: part_of p cG -> iPart_of p (ig_end cG)
  | ipof_from F T C: iPart_of F (ig_msg None F T C)
  | ipof_to o F T C: iPart_of T (ig_msg o F T C)
  | ipof_cont p o F T C L G Ty: C L = Some (Ty, G)
    -> iPart_of p G -> iPart_of p (ig_msg o F T C).

Lemma rgend_part p G : part_of_all p G -> G = rg_end -> False.
Proof. by move=>[]. Qed.

Lemma pall_inv F T C G p :
  part_of_all p G -> G = rg_msg F T C -> F <> p -> T <> p ->
  (forall l Ty G, C l = Some (Ty, G) -> part_of_all p G).
Proof.
    by move=>[ F' T' C' [->]//
             | F' T' C' [_ ->]//
             |{}p F' T' C' ALL [_ _ <-] _ _ l Ty {}G /ALL
             ].
Defined.

Fixpoint find_partsc p G (H : part_of_all p G) {struct H}
  : part_of_allT p G
  :=
  match G as G0 return G = G0 -> part_of_allT p G0 with
  | rg_msg F T C => fun EQ =>
                      match @eqP _ F p with
                      | ReflectT pF => match EQ, pF with
                                       | erefl, erefl => pallT_from F T C
                                       end
                      | ReflectF pF =>
                        match @eqP _ T p with
                        | ReflectT pT => match EQ, pT with
                                         | erefl, erefl => pallT_to F T C
                                         end
                        | ReflectF pT =>
                          pallT_cont F T
                                     (fun l Ty G Cl =>
                                        find_partsc (pall_inv H EQ pF pT Cl))
                        end
                      end
  | rg_end => fun E => match rgend_part H E with end
  end erefl.

Definition rg_unr (G : rg_ty) : ig_ty :=
  match G with
  | rg_msg F T C
      => ig_msg None F T
                (fun lbl =>
                  match C lbl with
                  | None => None
                  | Some (t, G) => Some (t, ig_end G)
                  end)
  | rg_end => ig_end rg_end
  end.
