From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Atom.
Require Import MPST.Role.
Require Import MPST.Forall.
Require Import MPST.LNVar.
Require Import MPST.Actions.

Declare Scope gty_scope.

Notation "K .lbl" := (K.1)   (at level 2, left associativity, format "K .lbl") : gty_scope.
Notation "K .mty" := (K.2.1) (at level 2, left associativity, format "K .mty") : gty_scope.
Notation "K .gty" := (K.2.2) (at level 2, left associativity, format "K .gty") : gty_scope.

Section Syntax.

  Inductive g_ty A :=
  | g_end
  | g_var (v : rvar)
  | g_rec (G : g_ty A)
  | g_msg (a : A) (p : role) (q : role) (Ks : seq (lbl * (mty * g_ty A))).

  Arguments g_end [_].
  Arguments g_var [_].

  Open Scope gty_scope.

  Notation gfv a := (g_var (Rvar.fv a)).
  Notation gbv n := (g_var (Rvar.bv n)).

  Fixpoint depth_gty A (a : g_ty A) :=
    match a with
    | g_end
    | g_var _ => 0
    | g_rec G => (depth_gty G).+1
    | g_msg _ _ _ K => (maximum (map (fun x=> depth_gty x.gty) K)).+1
    end.

  Fixpoint participants A (G : g_ty A) :=
    match G with
    | g_end
    | g_var _ => [::]
    | g_rec G => participants G
    | g_msg _ p q Ks => p::q::flatten [seq participants K.gty | K <- Ks]
    end.

  Lemma gty_ind1 :
    forall A (P : g_ty A -> Prop),
      P g_end ->
      (forall v, P (g_var v)) ->
      (forall G, P G -> P (g_rec G)) ->
      (forall m p q Ks, (forall K, member K Ks -> P K.gty) ->
                        P (g_msg m p q Ks)) ->
      forall g : g_ty A, P g.
  Proof.
    move=> A P P_end P_var P_rec P_msg; fix Ih 1; case.
    + by apply: P_end.
    + by apply: P_var.
    + by move=>G; apply: P_rec=>//.
    + move=>m p q Ks; apply: P_msg.
      apply/forall_member; elim: Ks.
      - by [].
      - move=> K Ks IhKs; split; first (by apply: Ih).
        apply: IhKs.
  Qed.

  Fixpoint eq_g_ty (A : eqType) (a b : g_ty A) :=
    match a, b with
    | g_end, g_end => true
    | g_var v1, g_var v2 => v1 == v2
    | g_rec G1, g_rec G2 => eq_g_ty G1 G2
    | g_msg m1 p1 q1 Ks1, g_msg m2 p2 q2 Ks2 =>
      (m1 == m2)
        && (p1 == p2)
        && (q1 == q2)
        && (fix eqL Ks1 Ks2 :=
              match Ks1, Ks2 with
              | [::], [::] => true
              | K1::Ks1, K2::Ks2 => (K1.lbl == K2.lbl)
                                      && (K1.mty == K2.mty)
                                      && eq_g_ty K1.gty K2.gty
                                      && eqL Ks1 Ks2
              | _, _ => false
              end) Ks1 Ks2
    | _, _ => false
    end.

  Definition eq_alt (A : eqType) (l r : lbl * (mty * g_ty A)) :=
    (l.lbl == r.lbl) && (l.mty == r.mty) && eq_g_ty l.gty r.gty.

  Lemma eqgty_all (A : eqType) m1 p1 q1 (Ks1 : seq (lbl * (mty * g_ty A))) m2 p2 q2 Ks2 :
    eq_g_ty (g_msg m1 p1 q1 Ks1) (g_msg m2 p2 q2 Ks2) =
    (m1 == m2) && (p1 == p2) && (q1 == q2) && all2 (eq_alt (A:=A)) Ks1 Ks2.
  Proof.
    rewrite /=; do 3 (case: eqP=>///= _).
    by elim: Ks1 Ks2=>[|Ks1 K1 Ih]; case=>[|Ks2 K2]//; rewrite Ih.
  Qed.

  Lemma g_ty_eqP (A: eqType) : Equality.axiom (eq_g_ty (A:=A)).
  Proof.
    rewrite /Equality.axiom; fix Ih 1 => x y.
    case x =>[|vl| Gl |ml pl ql Ksl]; case y =>[|vr| Gr |mr pr qr Ksr];
      try (by constructor).
    + by rewrite /eq_g_ty; case: eqP=>[->|H];constructor=>//[[]].
    + by rewrite /=; case: Ih=>[->|H];constructor=>//[[]].
    + rewrite eqgty_all; do 3 (case: eqP=>[<-|H];[|constructor=>[[]]//] =>/=).
      elim: Ksl Ksr =>[|[ll [tl Gl]] Ksl IhKs].
      - case; try (by constructor).
      - move=>[|[lr [tr Gr] Ksr]/=]; first (by constructor).
        rewrite /eq_alt/=; do 2 (case: eqP=>[->|F];[|constructor=>[[/F]]//]).
        case: Ih=>[->|F]/=;[|constructor=>[[/F]]//].
        by case: IhKs=>[[]<-|F]; constructor=>//[[F']]; move: F' F=>->.
  Qed.

  Definition g_ty_eqMixin (A : eqType) := EqMixin (g_ty_eqP (A:=A)).
  Canonical g_ty_eqType (A: eqType) := Eval hnf in EqType (g_ty A) (g_ty_eqMixin A).

  Lemma alt_eqP (A : eqType) : Equality.axiom (eq_alt (A:=A)).
  Proof.
    rewrite /Equality.axiom/eq_alt; move=>[l1  [t1 Ks1]] [l2 [t2 Ks2]]/=.
    do 2 (case: eqP=>[<-|H]; last (by apply: ReflectF => [[/H]])).
    by case: g_ty_eqP=>[<-|H]; last (by apply: ReflectF =>[[/H]]); apply: ReflectT.
  Qed.

  Lemma gty_ind2 :
    forall A (P : g_ty A -> Prop),
      P g_end ->
      (forall v, P (g_var v)) ->
      (forall G, P G -> P (g_rec G)) ->
      (forall m p q Ks, Forall (fun K => P K.gty) Ks -> P (g_msg m p q Ks)) ->
      forall G : g_ty A, P G.
  Proof.
    move=> A P P_end P_var P_rec P_msg; elim/gty_ind1=>//.
    by move=> m p q Ks /forall_member; apply: P_msg.
  Qed.

  Fixpoint g_open A (d : nat) (G2 : g_ty A) (G1 : g_ty A) :=
    match G1 with
    | g_end => G1
    | g_var v => Rvar.open (@g_var A) d G2 v
    | g_rec G => g_rec (g_open d.+1 G2 G)
    | g_msg m p q Ks =>
      g_msg m p q [seq (K.lbl, (K.mty, g_open d G2 K.gty)) | K <- Ks]
    end.
  Notation "{ k '~>' v } G":= (g_open k v G) (at level 30, right associativity).
  Notation "G '^' v":= (g_open 0 (gfv v) G) (at level 30, right associativity).

  Fixpoint g_close A (v : atom) (d : nat) (G1 : g_ty A) :=
    match G1 with
    | g_end => G1
    | g_var gv => g_var (Rvar.close v d gv)
    | g_rec G => g_rec (g_close v d.+1 G)
    | g_msg m p q Ks => g_msg m p q [seq (K.lbl, (K.mty, g_close v d K.gty)) | K <- Ks]
    end.
  Notation "{ k '<~' v } G":= (g_close v k G) (at level 30, right associativity).

  Definition fsetUs (K : choiceType) : seq {fset K} -> {fset K}
    := foldl fsetU fset0.

  Lemma fsetUs_cons (K : choiceType) (x : K) s L :
    x \in fsetUs (s :: L) = (x \in s) || (x \in fsetUs L).
  Proof.
    rewrite /fsetUs/=.
    elim: L fset0 => [s'|s' L Ih s'']/=; first (by rewrite in_fsetU orbC).
    by rewrite fsetUC fsetUA Ih fsetUC.
  Qed.

  Open Scope fset_scope.
  Fixpoint g_fvar A (G : g_ty A) : {fset atom} :=
    match G with
    | g_var v => Rvar.fvar v
    | g_rec G => g_fvar G
    | g_msg m p q Ks => fsetUs [seq g_fvar K.gty | K <- Ks]
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

  Fixpoint g_fbvar A (d : nat) (G : g_ty A) : {fset nat} :=
    match G with
    | g_var v => Rvar.fbvar d v
    | g_rec G => g_fbvar d.+1 G
    | g_msg m p q Ks => fsetUs [seq g_fbvar d K.gty | K <- Ks]
    | g_end => fset0
    end.

  Definition g_lc A (G : g_ty A) := g_fbvar 0 G = fset0.

  Lemma in_gfvar_gfv A (a a' : atom) : (a \in g_fvar (A:=A) (gfv a')) = (a == a').
  Proof.
    rewrite /g_fvar; case: fset1P=>[->|].
    - by rewrite eq_refl.
    - by move=> /eqP/negPf->.
  Qed.

  Lemma gopen_gfv A n X (a : atom) : g_open n X (A:=A) (gfv a) = gfv a.
  Proof. by []. Qed.

  Lemma gclose_gfv A n X (a : atom) :
    g_close (A:=A) X n (gfv a) = if X == a then (gbv n) else (gfv a).
  Proof. by rewrite /g_close/Rvar.close (fun_if (@g_var A)). Qed.

  Lemma g_open_close A X (G : g_ty A) n : X \notin g_fvar G -> {n <~ X}{n ~> gfv X}G = G.
  Proof.
    elim/gty_ind1: G n =>//.
    - by move=> v d /= H; rewrite Rvar.open_fun /= (Rvar.open_close d H).
    - move=> G Ih d; rewrite /g_fvar -/(g_fvar _)=>/Ih-{Ih}Ih.
      by rewrite -[in RHS](Ih d.+1).
    - move=> m p q Ks Ih n /= H; rewrite -map_comp/comp/=; congr g_msg.
      elim: Ks H Ih => {p} {q} [//|/=[l [t G]] Ks Ih].
      rewrite fsetUs_cons negb_or /= =>/andP-[X_G X_KS] IhKs.
      rewrite (IhKs (l, (t, G)) (or_introl (Logic.eq_refl _)) n X_G) Ih //.
      by move=> K KKs r H; apply: IhKs =>//; right.
  Qed.

  Lemma g_close_open A n X (G : g_ty A) : n \notin g_fbvar 0 G -> {n ~> gfv X}{n <~ X}G = G.
  Proof.
    move: {1 3}n (add0n n)=>n0; elim/gty_ind2: G 0 n =>///=.
    - by move=> v n n1 <- H; rewrite addnC Rvar.open_fun Rvar.close_open.
    - move=> G Ih d n Eq n_in; congr g_rec; apply: (Ih d.+1)=>//.
      by rewrite -Eq.
    - move=> m p q Ks /Fa_lift-Fa d n Eq; rewrite notin_fold_all !all_map /preim/=.
      move: (Fa d)=>{Fa}/Fa_lift/(_ n)/Fa_lift/(_ Eq)-Fa.
      move=>/forallbP/(Fa_conj Fa){Fa}.
      rewrite /SimplPred/= =>/Fa_app/Fa_map_eq-Ih.
      rewrite -map_comp /comp/=; congr g_msg => {Eq d n0 p q}.
      by elim: Ks Ih=>[//|/=[l [t G]] Ks Ih [-> /Ih->]].
  Qed.
  Close Scope fset_scope.

  Lemma g_depth_open A (G : g_ty A) X : depth_gty G = depth_gty (G^X).
  Proof.
    move: 0; elim/gty_ind2: G=>/=//.
    + by move=>v n; rewrite Rvar.open_fun.
    + by move=> G Ih n; rewrite (Ih n.+1).
    + move=> _ _ _ Gs /Fa_lift-Ih n; move: (Ih n) => {Ih}/Fa_map_eq.
      rewrite -map_comp /comp/=.
      by elim: Gs=>[//|/=[l G] Gs Ih []<- /Ih-{Ih}[<-]].
  Qed.

  (* Induction scheme that takes into account that g_rec must be opened *)
  Lemma gty_ind3 :
    forall (A :eqType) (P : g_ty A -> Type),
      P g_end ->
      (forall v, P (g_var v)) ->
      (forall G, (forall X (s : {fset atom}), X \notin s -> P (G ^ X)) ->
                 P (g_rec G)) ->
      (forall m p q Ks, (forall K, K \in Ks -> P K.gty) -> P (g_msg m p q Ks)) ->
      forall g : g_ty A, P g.
  Proof.
    move=> A P P_end P_var P_rec P_msg G.
    move: {-1}(depth_gty G) (leqnn (depth_gty G))=> n; move: n G; elim.
    + by case.
    + move=>n Ih; case=>///=.
      - by move=> G dG; apply: P_rec => X S _; apply: Ih; rewrite -g_depth_open.
      - move=>m p q Ks dKs; apply: P_msg=>K /(map_f (fun X => depth_gty X.gty))/=.
        move=>/in_maximum_leq-dG; move: (leq_trans dG dKs)=>{dG} {dKs}.
        by apply: Ih.
  Qed.
  Close Scope gty_scope.
End Syntax.

Section Semantics.

  Definition rg_ty := g_ty (option lbl).

  Open Scope gty_scope.

  Inductive step : act -> rg_ty -> rg_ty -> Prop :=
  (* Basic rules *)
  | st_send (lb : lbl) p q (Ks : seq (lbl * (mty * rg_ty))) :
      lb \in [seq K.1 | K <- Ks] ->
      step (a_sel p q lb) (g_msg None p q Ks) (g_msg (Some lb) p q Ks)
  | st_recv (lb : lbl) p q (Ks : seq (lbl * (mty * rg_ty))) t G :
      lookup lb Ks == Some (t, G) ->
      step (a_brn p q lb) (g_msg (Some lb) p q Ks) G
  .
           (*

  (* Asynchronous *)
  | st_amsg a p G G' :
      subject a \notin [:: p.1.1; p.1.2] ->
      step a G G' ->
      step a (rg_msg p G) (rg_msg p G')
  | st_arcv a p G G' :
      subject a != p.1.2 ->
      step a G G' ->
      step a (rg_rcv p G) (rg_rcv p G')
  | st_abrn a p K K' :
      subject a \notin [:: p.1.1; p.1.2] ->
      step_all a K K' ->
      step a (rg_brn p K) (rg_brn p K')
  | st_aalt a lb p K K' :
      subject a != p.1.2 ->
      step_only lb a K K' ->
      step a (rg_alt lb p K) (rg_alt lb p K')

  (* Structural *)
  | st_rec l G G' :
      step l (rg_open 0 G (rg_rec G)) G' ->
      step l (rg_rec G)               G'
  with step_all : act -> seq (lbl * rg_ty) -> seq (lbl * rg_ty) -> Prop :=
       | st_nil a : step_all a [::] [::]
       | st_cons a G G' K K' lb :
           step a G G' ->
           step_all a K K' ->
           step_all a ((lb, G) :: K) ((lb, G') :: K')
  with step_only : lbl -> act -> seq (lbl * rg_ty) -> seq (lbl * rg_ty) -> Prop :=
       | st_this a G G' K lb :
           step a G G' ->
           step_only lb a ((lb, G) :: K) ((lb, G') :: K)
       | st_next a lG K K' lb  :
           lb != lG.1 ->
           step_only lb a K K' ->
           step_only lb a (lG :: K) (lG :: K')
  .
*)

  Derive Inversion step_inv with (forall a G G', step a G G') Sort Prop.

  (*
  Scheme step_ind1 := Induction for step Sort Prop
  with stepall_ind1 := Induction for step_all Sort Prop
  with steponly_ind1 := Induction for step_only Sort Prop.
  *)

  CoInductive g_lts : trace -> rg_ty -> Prop :=
  | eg_end : g_lts tr_end g_end
  | eg_trans a t G G' :
      step a G G' ->
      g_lts t G' ->
      g_lts (tr_next a t) G.

  Derive Inversion glts_inv with (forall tr G, g_lts tr G) Sort Prop.

End Semantics.

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
