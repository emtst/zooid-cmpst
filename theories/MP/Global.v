From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.MP.Atom.
Require Import MPST.MP.Role.
Require Import MPST.MP.Forall.
Require Import MPST.MP.LNVar.

Section Syntax.
  Definition g_prefix := ((role * role) * mty)%type.

  Inductive g_ty :=
  | g_end
  | g_var (v : rvar)
  | g_rec (G : g_ty)
  | g_msg (p : g_prefix) (G : g_ty)
  | g_brn (p : g_prefix) (K : seq (lbl * g_ty)).

  Notation gfv a := (g_var (Rvar.fv a)).
  Notation gbv n := (g_var (Rvar.bv n)).

  Fixpoint depth_gty a :=
    match a with
    | g_end
    | g_var _ => 0
    | g_rec G
    | g_msg _ G => (depth_gty G).+1
    | g_brn p K => (maximum (map (fun x=> depth_gty x.2) K)).+1
    end.

  Fixpoint participants G :=
    match G with
    | g_end
    | g_var _ => [::]
    | g_rec G => participants G
    | g_msg ((p, q), _) G => p::q::participants G
    | g_brn ((p, q), _) K => p::q::flatten [seq participants x.2 | x <- K]
    end.

  Lemma gty_ind1 :
    forall (P : g_ty -> Prop),
      P g_end ->
      (forall v, P (g_var v)) ->
      (forall G, P G -> P (g_rec G)) ->
      (forall p G, P G -> P (g_msg p G)) ->
      (forall p Gs, (forall lG, member lG Gs -> P lG.2) -> P (g_brn p Gs)) ->
      forall g : g_ty, P g.
  Proof.
    move=> P P_end P_var P_rec P_msg P_branch; fix Ih 1; case.
    + by apply: P_end.
    + by apply: P_var.
    + by move=>G; apply: P_rec=>//.
    + by move=>p G; apply: P_msg=>//.
    + move=>p Gs; apply: P_branch; apply/forall_member; elim Gs.
      - by [].
      - move=> lG1 {Gs}Gs IhGs/=; split; first by apply Ih.
        apply: IhGs.
  Qed.

  Fixpoint eq_g_ty a b :=
    match a, b with
    | g_end, g_end => true
    | g_var v1, g_var v2 => v1 == v2
    | g_rec G1, g_rec G2 => eq_g_ty G1 G2
    | g_msg p1 G1, g_msg p2 G2 => (p1 == p2) && eq_g_ty G1 G2
    | g_brn p1 K1, g_brn p2 K2 =>
      (p1 == p2)
        && (fix eqL K1 K2 :=
              match K1, K2 with
              | [::], [::] => true
              | l::K1, r::K2 => (l.1 == r.1) && eq_g_ty l.2 r.2 && eqL K1 K2
              | _, _ => false
              end) K1 K2
    | _, _ => false
    end.

  Definition eq_alt (l r : lbl * g_ty) := (l.1 == r.1) && eq_g_ty l.2 r.2.

  Lemma eqgty_all p1 K1 p2 K2 :
    eq_g_ty (g_brn p1 K1) (g_brn p2 K2) =
    (p1 == p2) && all2 eq_alt K1 K2.
  Proof.
    rewrite /=; case: eqP=>///= _ {p1 p2}.
    by move: K2; elim: K1=>[|lG1 K1 Ih]; case=>[|lG2 K2]/=//; rewrite Ih.
  Qed.

  Lemma g_ty_eqP : Equality.axiom eq_g_ty.
  Proof.
    rewrite /Equality.axiom; fix Ih 1 => x y.
    case x =>[|vl| Gl |pl Gl| pl Gsl]; case y =>[|vr| Gr |pr Gr| pr Gsr];
      try (by constructor).
    + by rewrite /eq_g_ty; case: eqP=>[->|H];constructor=>//[[]].
    + by rewrite /=; case: Ih=>[->|H];constructor=>//[[]].
    + by rewrite /=; case:eqP=>[->|H]; case: Ih=>[->|H'];constructor=>//[[]].
    + rewrite eqgty_all; case: eqP=>[<-|H];[|constructor=>[[]]//] =>/=.
      elim: Gsl Gsr.
      - by case; constructor.
      - move=>[ll Gl] Gsl Ih' [|[lr Gr] Gsr] /=; try (by constructor).
        rewrite /eq_alt/=; case: eqP=>[->|F];[|constructor=>[[/F]]//].
        case: Ih=>[<-|F];[|constructor=>[[/F]]//].
        by case: Ih'=>[[]<-|F];constructor=>//[[F']]; move: F' F=>->.
  Qed.

  Definition g_ty_eqMixin := EqMixin g_ty_eqP.
  Canonical g_ty_eqType := Eval hnf in EqType g_ty g_ty_eqMixin.

  Lemma alt_eqP : Equality.axiom eq_alt.
  Proof.
    rewrite /Equality.axiom/eq_alt; move=>[l1 G1] [l2 G2]/=.
    case: eqP=>[<-|H]; last (by apply: ReflectF => [[/H]]).
    by case: g_ty_eqP=>[<-|H]; last (by apply: ReflectF =>[[/H]]); apply: ReflectT.
  Qed.

  Lemma gty_ind2 :
    forall (P : g_ty -> Prop),
      P g_end ->
      (forall v, P (g_var v)) ->
      (forall G, P G -> P (g_rec G)) ->
      (forall p G, P G -> P (g_msg p G)) ->
      (forall p Gs, Forall (fun lG => P lG.2) Gs -> P (g_brn p Gs)) ->
      forall g : g_ty, P g.
  Proof.
    move=> P P_end P_var P_rec P_msg P_branch; elim/gty_ind1=>//.
    by move=> p Gs /forall_member; apply: P_branch.
  Qed.

  Fixpoint g_open (d : nat) (G2 : g_ty) (G1 : g_ty) :=
    match G1 with
    | g_end => G1
    | g_var v => Rvar.open g_var d G2 v
    | g_rec G => g_rec (g_open d.+1 G2 G)
    | g_msg p G => g_msg p (g_open d G2 G)
    | g_brn p Gs => g_brn p [seq (lG.1, g_open d G2 lG.2) | lG <- Gs]
    end.
  Notation "{ k '~>' v } G":= (g_open k v G) (at level 30, right associativity).
  Notation "G '^' v":= (g_open 0 (gfv v) G) (at level 30, right associativity).

  Fixpoint g_close (v : atom) (d : nat) (G1 : g_ty) :=
    match G1 with
    | g_end => G1
    | g_var gv => g_var (Rvar.close v d gv)
    | g_rec G => g_rec (g_close v d.+1 G)
    | g_msg p G => g_msg p (g_close v d G)
    | g_brn p Gs => g_brn p [seq (lG.1, g_close v d lG.2) | lG <- Gs]
    end.
  Notation "{ k '<~' v } G":= (g_close v k G) (at level 30, right associativity).

  Definition fsetUs (K : choiceType) : seq {fset K} -> {fset K}
    := foldl fsetU fset0.

  Open Scope fset_scope.
  Fixpoint g_fvar (G : g_ty) : {fset atom} :=
    match G with
    | g_var v => Rvar.fvar v
    | g_rec G
    | g_msg _ G => g_fvar G
    | g_brn _ Gs => fsetUs [seq g_fvar lG.2 | lG <- Gs]
    | g_end => fset0
    end.

  Lemma in_fold_has (A : choiceType) (x : A) (l : seq {fset A}) :
    (x \in fsetUs l) = has (fun s => x \in s) l.
  Proof.
    rewrite /fsetUs.
    rewrite -[has (fun s => x \in s) l]/(false || has (fun s => x \in s) l).
    rewrite -(in_fset0 x); elim: l fset0.
    + by move=>z; rewrite Bool.orb_false_r.
    + by move=> a l Ih z/=; rewrite Ih in_fsetU orbA.
  Qed.

  Lemma notin_fold_all (A : choiceType) (x : A) (l : seq {fset A}) :
    (x \notin fsetUs l) = all (fun s => x \notin s) l.
  Proof. by rewrite in_fold_has -all_predC. Qed.

  Fixpoint g_fbvar (d : nat) (G : g_ty) : {fset nat} :=
    match G with
    | g_var v => Rvar.fbvar d v
    | g_rec G => g_fbvar d.+1 G
    | g_msg _ G => g_fbvar d G
    | g_brn _ Gs => fsetUs [seq g_fbvar d lG.2 | lG <- Gs]
    | g_end => fset0
    end.

  Definition g_lc (G : g_ty) := g_fbvar 0 G = fset0.

  Lemma in_gfvar_gfv (a a' : atom) : (a \in g_fvar (gfv a')) = (a == a').
  Proof.
    rewrite /g_fvar; case: fset1P=>[->|].
    - by rewrite eq_refl.
    - by move=> /eqP/negPf->.
  Qed.

  Lemma gopen_gfv n X (a : atom) : {n ~> X} gfv a = gfv a.
  Proof. by []. Qed.

  Lemma gclose_gfv n X (a : atom) :
    {n <~ X} gfv a = if X == a then (gbv n) else (gfv a).
  Proof. by rewrite /g_close/Rvar.close (fun_if g_var). Qed.

  Lemma g_open_close X G n : X \notin g_fvar G -> {n <~ X}{n ~> gfv X}G = G.
  Proof.
    elim/gty_ind2: G n =>//.
    - by move=> v d /= H; rewrite Rvar.open_fun /= (Rvar.open_close d H).
    - move=> G Ih d; rewrite /g_fvar -/(g_fvar _)=>/Ih-{Ih}Ih.
      by rewrite -[in RHS](Ih d.+1).
    - move=> p G Ih d; rewrite /g_fvar -/(g_fvar _)=>/Ih-{Ih}Ih.
      by rewrite -[in RHS](Ih d).
    - move=> p Gs /Fa_lift-Ih n; move: (Ih n)=>{Ih}Ih.
      rewrite notin_fold_all -/g_fvar all_map /preim/=.
      rewrite /SimplPred/= -map_comp/comp/= =>/forallbP/=.
      move=>/(Fa_conj Ih)/Fa_app{Ih}/Fa_map_eq-Ih; congr g_brn.
      by elim: Gs Ih=>[//|[l G] Gs /= Ih [->/Ih->]].
  Qed.

  Lemma g_close_open n X G : n \notin g_fbvar 0 G -> {n ~> gfv X}{n <~ X}G = G.
  Proof.
    move: {1 3}n (add0n n)=>n0; elim/gty_ind2: G 0 n =>///=.
    - by move=> v n n1 <- H; rewrite addnC Rvar.open_fun Rvar.close_open.
    - move=> G Ih d n Eq n_in; congr g_rec; apply: (Ih d.+1)=>//.
      by rewrite -Eq.
    - by move=> p G Ih d n Eq n_in; congr g_msg; apply: (Ih d).
    - move=> p Gs /Fa_lift-Fa d n Eq; rewrite notin_fold_all !all_map /preim/=.
      move: (Fa d)=>{Fa}/Fa_lift/(_ n)/Fa_lift/(_ Eq)-Fa.
      move=>/forallbP/(Fa_conj Fa){Fa}.
      rewrite /SimplPred/= =>/Fa_app/Fa_map_eq-Ih.
      rewrite -map_comp /comp/=; congr g_brn => {Eq} {d} {n0} {p}.
      by elim: Gs Ih=>[//|/=[l G] Gs Ih [-> /Ih->]].
  Qed.
  Close Scope fset_scope.

  Lemma g_depth_open G X : depth_gty G = depth_gty (G^X).
  Proof.
    move: 0; elim/gty_ind2: G=>/=//.
    + by move=>v n; rewrite Rvar.open_fun.
    + by move=> G Ih n; rewrite (Ih n.+1).
    + by move=> _ G Ih n; rewrite (Ih n).
    + move=> _ Gs /Fa_lift-Ih n; move: (Ih n) => {Ih}/Fa_map_eq.
      rewrite -map_comp /comp/=.
      by elim: Gs=>[//|/=[l G] Gs Ih []<- /Ih-{Ih}[<-]].
  Qed.

  (* Induction scheme that takes into account that g_rec must be opened *)
  Lemma gty_ind3 :
    forall (P : g_ty -> Type),
      P g_end ->
      (forall v, P (g_var v)) ->
      (forall G, (forall X (s : {fset atom}), X \notin s -> P (G ^ X)) ->
                 P (g_rec G)) ->
      (forall p G, P G -> P (g_msg p G)) ->
      (forall p Gs, (forall l G, (l, G) \in Gs -> P G) -> P (g_brn p Gs)) ->
      forall g : g_ty, P g.
  Proof.
    move=> P P_end P_var P_rec P_msg P_brn G.
    move: {-1}(depth_gty G) (leqnn (depth_gty G))=> n; move: n G; elim.
    + by case.
    + move=>n Ih; case=>///=.
      - by move=> G dG; apply: P_rec => X S _; apply: Ih; rewrite -g_depth_open.
      - by move=> p G dG; apply: P_msg; apply: Ih.
      - move=> p Gs dGs; apply: P_brn => l G /(map_f (fun X => depth_gty X.2))/=.
        move=>/in_maximum_leq-dG; move: (leq_trans dG dGs)=>{dG} {dGs}.
        by apply: Ih.
  Qed.
End Syntax.

(*
r0 -> r1. r1 -> r0. r1 -> r2. r2 -> r1
C0 < C1
C1 < C0
C1 < C2
C2 < C1

0 - 1 |- 0
      |- 2 - 1

0 - 1 - 0 (c0 + c1)

0 - 1 - 2 (c0 + c1)


[0, 1, 0] [1, 2, 1] [0, 1, 2, 1]

[0,1]
[0,1,0]
[0,1,0] [1,2]
[0,1,0] [1,2,1]

[0, 1, 2] <- 1-0
[0, 1, 0] [1, 2, 1]



                  C0 = C1     | c0   ==== C1 + c0
                  C1 = C0, C2 | c1   ==== C0 + c1 | C2 + c1
                  C2 = C1     | c2   ====

cost C = [r |-> max (cost^C [C(r)])(r) ]_r\in C
cost^C [] [0] = cost^C [(0,c0)] [1]
              = cost^C [(1, c1), (0, c0)] [0, 2]
              = cost^C [(0, c0 + c1), (1, c1)] [2]
              = cost^C [(2, c2), (0, c0 + c1), (1, c1)] [1]
              = cost^C [(2, c2 + c1)]

cost [1,0] (C0, C2 | c1) =
cost [2, 1,0] (C1 | c1) =

 T0 =
 T1 = max (c0 + c1, c1 + c2)
 T2 = max (c0 + c1, c1 + c2)
                  C0 = C1, C0, C2 | c0
                  C1 = C0, C1, C2 | c1
                  C2 = C0, C1 | c2

                  C0 = C0, C1 | c0
                  C1 = C0, C1 | c1
                  C2 = C0, C1 | c2
    C0 + C1 , C0 + C1 , max(C0 + C1, C1 + C2)

T0 = ts + tr + c1 + ts + tr + t0
T1 = ts + tr + c1 + ts + tr + t0
                                T2 = tr + ts + tr + t0 + c1 + ts + tr + c2
*)
