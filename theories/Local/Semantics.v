From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco2.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.

Require Import MPST.Local.Syntax.
Require Import MPST.Local.Tree.
Require Import MPST.Local.Unravel.

Notation renv := {fmap role -> rl_ty}.
Notation qenv := {fmap role * role -> seq (lbl * mty) }.

Definition enq (qs : {fmap (role * role) -> (seq (lbl * mty))}) k v :=
  match qs.[? k] with
  | Some vs => qs.[ k <- app vs [:: v] ]
  | None => qs.[ k <- [:: v]]
  end%fmap.

Definition deq (qs : {fmap (role * role) -> (seq (lbl * mty))}) k :=
  match qs.[? k] with
  | Some vs =>
    match vs with
    | v :: vs => if vs == [::] then Some (v, qs.[~ k])
                 else Some (v, qs.[k <- vs])
    | [::] => None
    end
  | None => None
  end%fmap.

Definition look (E : {fmap role -> rl_ty}) p := odflt rl_end E.[? p]%fmap.

Definition do_act_lt (L : rl_ty) A :=
let: (mk_act a p q l t) := A in
match L with
| rl_msg a' q' Ks =>
  match Ks l with
  | Some (t', Lp) =>
    if (a == a') && (q == q') && (t == t')
    then Some Lp
    else None
  | None => None
  end
| _ => None
end%fmap.

Definition run_act_lt (L : rl_ty) A := odflt L (do_act_lt L A).

Definition do_act (P : renv) A :=
  let: (mk_act a p q l t) := A in
  match do_act_lt (look P p) A with
  | Some Lp => Some (P.[p <- Lp]%fmap)
  | None => None
  end.

Lemma doact_send (E : renv) p q lb t KsL Lp :
  (look E p = rl_msg l_send q KsL) ->
  (KsL lb = Some (t, Lp)) ->
  exists E', (do_act E (mk_act l_send p q lb t) = Some E').
Proof.
  move=>H1 H2; rewrite /do_act/do_act_lt H1 H2 !eq_refl/=.
  by exists E.[ p <- Lp]%fmap.
Qed.

Definition do_act_l_ty (L: l_ty) (A : act) : option l_ty :=
  let: (mk_act a p q l t) := A in
  match lunroll (lrec_depth L) L with
  | l_msg a' q' Ks =>
    match find_cont Ks l with
    | Some (t', Lp) =>
      if (a == a') && (q == q') && (t == t')
      then Some Lp
      else None
    | None => None
    end
  | _ => None
  end.

Definition run_act_l_ty (L: l_ty) (A : act) : l_ty := odflt L (do_act_l_ty L A).

Lemma do_act_works Li Lr A :
  LUnroll Li Lr -> LUnroll (run_act_l_ty Li A) (run_act_lt Lr A).
Proof.
  rewrite /run_act_l_ty/run_act_lt/do_act_l_ty/do_act_lt/==>LU.
  case: A=> a _ q l t; move: ((LUnroll_ind (lrec_depth Li) Li Lr).1 LU)=>LU'.
  move: LU' LU.
  case EQ: (lunroll (lrec_depth Li) Li)=> [| v | Li' | a' p C].
  - by move=> /lunroll_end->.
  - by move=>/(paco2_unfold l_unroll_monotone); case F: _ _ /.
  - by move=>/= _ _; apply/(lunroll_inf _ EQ).
  - move=>/(paco2_unfold l_unroll_monotone).
    case F: _ _ / =>[||a0 p0 K0 C0 DOM UNR]//.
    move: F DOM UNR=>[<-<-<-] DOM UNR{a0 p0 K0 EQ}.
    case EQ: find_cont=>[[Ty L]|]//; last by rewrite (dom_none DOM EQ).
    move: (dom DOM EQ)=>[{}Lr] EQ'; rewrite EQ'/=.
    case: (boolP ((a == a') && (q == p) && (t == Ty)))=>//= _ _.
    by move: (UNR _ _ _ _ EQ EQ')=>[].
Qed.

Open Scope fmap_scope.
(** lstep a Q P Q' P' is the 'step' relation <P, Q> ->^a <P', Q'> in Coq*)
Inductive lstep : act -> renv * qenv -> renv * qenv -> Prop :=
| ls_send t p q lb (P P' : renv) (Q Q' : qenv) :
    Q' == enq Q (p, q) (lb, t) ->
    do_act P (mk_act l_send p q lb t) = Some P' ->
    lstep (mk_act l_send p q lb t) (P, Q) (P', Q')
| ls_recv t p q lb (P P' : renv) (Q Q' : qenv) :
    deq Q (p, q) == Some ((lb, t), Q') ->
    do_act P (mk_act l_recv q p lb t) = Some P' ->
    lstep (mk_act l_recv q p lb t) (P, Q) (P', Q')
.
Derive Inversion lstep_inv with (forall A P P', lstep A P P') Sort Prop.

Definition runnable (A : act) (P : renv * qenv) : bool :=
  match do_act P.1 A with
  | Some _ =>
    let: mk_act a p q l t := A in
    match a with
    | l_send => true
    | l_recv =>
      match deq P.2 (q, p) with
      | Some ((l', t'), Q) => (l == l') && (t == t')
      | None => false
      end
    end
  | None => false
  end.

Lemma lstep_runnable A P P' : lstep A P P' -> runnable A P.
Proof.
  by case=> Ty F T l {P P'}E E' Q Q' /eqP-QFT /=; case LOOK: look=>[|a p C]//;
     case Cl: (C l)=>[[Ty' L]|]//; case: ifP=>//EQ _;
     rewrite /runnable/= LOOK Cl EQ // QFT !eq_refl.
Qed.

Lemma lstep_eq A P P0 P1 : lstep A P P0 -> lstep A P P1 -> P0 = P1.
Proof.
  case=>Ty0 F0 T0 l0 {P P0}E E0 Q Q0 /eqP-QFT/=; case LOOK: look=>[|a p C]//;
  case Cl: (C l0)=>[[Ty' L]|]//; case: ifP=>//EQ [<-];
  elim/lstep_inv =>// _ Ty1 F1 T1 l1 E' E1 Q' Q1 /eqP-QFT'/= ACT EQ1 EQ2 EQ3;
  move: EQ1 EQ2 EQ3 ACT QFT QFT'=>[->->->->] [->->] _ {F1 T1 l1 Ty1 E' Q' P1};
  rewrite LOOK Cl EQ=>[][<-]->.
  - by move=>->.
  - by move=>[->].
Qed.

Definition do_queue (Q : qenv) (A : act) : qenv :=
  match A with
  | mk_act l_send F T l Ty => enq Q (F, T) (l, Ty)
  | mk_act l_recv F T l Ty =>
    match deq Q (T, F) with
    | Some (_, Q') => Q'
    | None => Q
    end
  end.

(* Attempts to run a step, does nothing if it cannot run *)
Definition run_step (A : act) (P : renv * qenv) : renv * qenv :=
  match do_act P.1 A with
  | Some E' => (E', do_queue P.2 A)
  | _ => P
  end.

(* Lemma run_step 'makes sense' *)
Lemma run_step_sound A P : runnable A P -> lstep A P (run_step A P).
Proof.
  case: P => E Q.
  rewrite /runnable /=; case E_doact: (do_act _ _)=>[E'|//].
  case: A E_doact=> [[|] p q l t E_doact]/=.
  - by move=> _; rewrite /run_step E_doact; constructor=>//.
  - case E_deq: (deq _ _) =>[[[l' t'] Q']|//].
    case: (boolP ((l == l') && _)) =>[/andP-[/eqP-ll' /eqP-tt']|//] _.
    move: ll' tt' E_deq =><-<- E_deq.
    rewrite /run_step E_doact /= E_deq.
      by constructor =>//; first by apply/eqP.
Qed.

Lemma run_step_compl A P P' : lstep A P P' -> P' = run_step A P.
Proof.
  by move=> ST; move: (lstep_runnable ST)=>/run_step_sound/(lstep_eq ST).
Qed.

Definition rel_trc := trace act -> renv*qenv -> Prop.
Inductive l_lts_ (r : rel_trc) : rel_trc :=
| lt_end E :
    (forall p, look E p = rl_end) ->
    @l_lts_ r (tr_end _) (E, [fmap])
| lt_next a t P P' :
    lstep a P P' ->
    r t P' ->
    @l_lts_ r (tr_next a t) P.
Hint Constructors l_lts_.
Lemma l_lts_monotone : monotone2 l_lts_.
Proof. pmonauto. Qed.
Hint Resolve l_lts_monotone : paco.

Definition l_lts t L := paco2 l_lts_ bot2 t L.
Derive Inversion llts_inv with (forall tr G, l_lts tr G) Sort Prop.

Definition rty_trc := trace act -> rl_ty -> Prop.
Inductive l_trc_ (p : role) (r : rty_trc) : rty_trc :=
| l_trc_end : l_trc_ p r (tr_end _) rl_end
| l_trc_msg A TR L L' :
    subject A == p -> do_act_lt L A = Some L' ->
    r TR L' ->
    l_trc_ p r (tr_next A TR) L
.
Lemma l_trc_monotone p : monotone2 (l_trc_ p).
Proof.
  move=>TR cL r r' Htrc MON; move: Htrc; case.
  - by constructor.
  - move=>A TR0 L L' Hsubj Hact /MON.
    by move: Hsubj Hact; apply l_trc_msg.
Qed.

Definition l_trc p t L := paco2 (l_trc_ p) bot2 t L.

Definition trc_rel := trace act -> trace act -> Prop.
Inductive subtrace_ (p : role) (r : trc_rel) : trc_rel :=
| subtrace_end : subtrace_ p r (tr_end _) (tr_end _)
| subtrace_skip A TRp TR :
    subject A != p ->
    r TRp TR ->
    subtrace_ p r TRp (tr_next A TR)
| subtrace_msg A TRp TR :
    subject A == p ->
    r TRp TR ->
    subtrace_ p r (tr_next A TRp) (tr_next A TR)
.
Lemma subtrace_monotone p : monotone2 (subtrace_ p).
Proof.
  move=>TR cL r r' Htrc MON; move: Htrc; case.
  - by constructor.
  - move=> A TRp TR0 Hsubj /MON; move: Hsubj.
    by apply: subtrace_skip.
  - move=> A TRp TR0 Hsubj /MON; move: Hsubj.
    by apply: subtrace_msg.
Qed.
Definition subtrace p T0 T1 := paco2 (subtrace_ p) bot2 T0 T1.
Hint Constructors EqL_.
Hint Resolve EqL_monotone.
Hint Resolve EqL_refl.

Notation cfg := (renv * qenv)%type.
