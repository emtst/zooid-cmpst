From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

From Paco Require Import paco paco2.

Require Import MPST.Atom.
Require Import MPST.AtomSets.
Require Import MPST.Forall.
Require Import MPST.LNVar.
Require Import MPST.Global.
Require Import MPST.Local.
Require Import MPST.Actions.
Require Import MPST.Projection.
Require Import MPST.WellFormed.
Require Import MPST.QProjection.

Section TraceEquiv.


  Open Scope mpst_scope.
  Open Scope fset.
  Open Scope fmap.

  Definition eProject (G: ig_ty) (E : {fmap role -> rl_ty}) : Prop :=
    forall p, IProj p G (look E p).



  Definition Projection G P := eProject G P.1 /\ qProject G P.2.



  Lemma doact_other p E A L :
    subject A != p -> match do_act E A with
                      | Some E' => Some E'.[p <- L]
                      | None => None
                      end = do_act E.[p <- L] A.
  Proof.
    case: A=>[a F T l Ty]; rewrite /do_act/look fnd_set => /=SUBJ.
    rewrite (negPf SUBJ).
    case: (E.[? F])=>[[//|a0 q C] |//].
    case: (C l)=>[[Ty' L']|//].
    case: ifP=>// _.
    by rewrite setfC eq_sym (negPf SUBJ).
  Qed.

  Lemma runnable_upd A E Q L p :
    subject A != p -> runnable A (E, Q) <-> runnable A (E.[p <- L], Q).
  Proof.
    move=> SUBJ; rewrite /runnable/= -doact_other//.
    by case: (do_act E A)=>[_|//].
  Qed.

  Lemma Proj_Some_next l F T C P :
    Projection (ig_msg (Some l) F T C) P ->
    forall Ty G,
      C l = Some (Ty, G) ->
      Projection G (run_step (mk_act l_recv T F l Ty) P).
  Proof.
    move=>[H qPRJ] Ty G Cl; move: (H T)=>PRJ.
    move: PRJ=>/IProj_recv_inv=>[[FT [CL [L_msg [DOM PRJ]]]]].
    move: (DOM l Ty)=>[/(_ (ex_intro _ _ Cl))-[L' CLl] _].
    move: qPRJ=>/qProject_Some_inv-[Ty' [G0 [Q [Cl' [DEQ qPRJ]]]]].
    move: Cl' DEQ qPRJ; rewrite Cl=> [[<-<-]] /eqP-DEQ QPRJ {Ty' G0}.
    rewrite /run_step/= L_msg CLl !eq_refl /= DEQ; split=>//.
    move=>p; case: (boolP (p == T)) =>[/eqP->|pT].
    - by rewrite /look fnd_set eq_refl; apply/(PRJ _ _ _ _ Cl CLl).
    - move: (H p)=>/IProj_send2_inv/(_ pT)-[_] [lC] [Ty0] [lCl] [DOM'] PRJ'.
      move: (DOM' l Ty)=>[/(_ (ex_intro _ _ Cl))-[L1 lCl'] _].
      move: lCl'; rewrite lCl=>[EQ]; move: EQ lCl=>[-> _] lCl {Ty0 L1}.
      rewrite  /look fnd_set (negPf pT) -/(look _ _).
      by apply: (PRJ' _ _ _ _ Cl lCl).
  Qed.

  Lemma look_comm E F L T (NEQ : F != T) :
    look E.[F <- L] T = look E T.
  Proof. by rewrite/look fnd_set eq_sym (negPf NEQ). Qed.


  Lemma Proj_None_next F T C P :
    Projection (ig_msg None F T C) P ->
    forall l Ty G,
      C l = Some (Ty, G) ->
      Projection G (run_step (mk_act l_recv T F l Ty)
                             (run_step (mk_act l_send F T l Ty) P)).
  Proof.
    move=>[H qPRJ] l Ty G Cl; move: (H F)=>PRJF.
    move: PRJF=>/IProj_send1_inv-[FT] [CF] [LF_E] [DOMF] PRJF.
    move: (DOMF l Ty) => [/(_ (ex_intro _ _ Cl))-[LF CFl] _].
    move: (H T)=>/IProj_recv_inv-[_] [CT] [LT_E] [DOMT] PRJT.
    move: (DOMT l Ty) => [/(_ (ex_intro _ _ Cl))-[LT CTl] _].
    move: qPRJ=>/qProject_None_inv-[PFT] qPRJ; split.
    - move=> p;
      case: (boolP (p == F)) =>[/eqP-> {p}|pF];
      [|case: (boolP (p == T)) =>[/eqP-> {pF p}|pT]].
      + (* p = F *)
        rewrite /look/run_step/= LF_E CFl !eq_refl/= look_comm // LT_E CTl.
        rewrite !eq_refl/= fnd_set (negPf FT) fnd_set eq_refl.
        by apply/(PRJF _ _ _ _ Cl).
      + (* p = T *)
        rewrite /look/run_step/= LF_E CFl !eq_refl /= look_comm // LT_E CTl.
        rewrite !eq_refl/= fnd_set eq_refl.
        by apply/(PRJT _ _ _ _ Cl).
      + (* T != p != F *)
        move: (H p)=>/IProj_mrg_inv/(_ pF)/(_ pT)-[_] [Cp] [DOMp] [PRJp] MRG.
        move: (DOMp l Ty) => [/(_ (ex_intro _ _ Cl))-[Lp' Cpl] _].
        move: (MRG _ _ _ Cpl)=>Lp_E.
        rewrite /run_step/= LF_E CFl !eq_refl/= look_comm// LT_E CTl.
        rewrite !eq_refl/= ?look_comm.
        by apply/(EqL_IProj _ Lp_E)/(PRJp _ _ _ _ Cl).
        by rewrite eq_sym.
        by rewrite eq_sym.
    - rewrite /run_step/= LF_E CFl !eq_refl /= look_comm // LT_E CTl !eq_refl/=.
      rewrite /enq PFT /deq fnd_set eq_refl /= remf1_set eq_refl.
      rewrite remf1_id; first by apply/qPRJ/Cl.
      by rewrite -fndSome PFT.
  Qed.

  Lemma doact_diff A E E' :
    do_act E A = Some E' -> exists L, E' = E.[subject A <- L].
  Proof.
    rewrite /do_act/do_act_lt/look/=; case: A=>[a p q l Ty]; case Ep: E.[? p] =>[[|ap r C]|]//.
    by case Cl: C=>[[Ty' L]|//]; case: ifP=>//= _ [/esym-H]; exists L.
  Qed.

  Definition fst_eq (A B : eqType) (x y : option (A * B)) :=
    match x, y with
    | Some (a, _), Some (b, _) => a == b
    | None, None => true
    | _, _ => false
    end.

  Lemma runnable_next_queue A E (Q Q' : {fmap role * role -> seq (lbl * mty)}) :
    (forall p, fst_eq (deq Q (p, subject A)) (deq Q' (p, subject A)))  ->
    runnable A (E, Q) <-> runnable A (E, Q').
  Proof.
    move=> H; rewrite /runnable; case: do_act=>// _.
    case: A H=>[[//|] p q l Ty]/= /(_ q).
    case: deq=>[[[lQ TyQ] WQ]|]; case: deq=>[[[lQ' TyQ'] WQ']|]//=.
    by rewrite xpair_eqE=>/andP-[/eqP<- /eqP<-].
  Qed.

  Lemma runnable_next A A' P :
    subject A != subject A' ->
    (subject A != object A') || (act_ty A' == l_recv) ->
    runnable A P <-> runnable A (run_step A' P).
  Proof.
    case A => [a p q l Ty]; case A'=>[a' p' q' l' Ty']/= NEQ COND.
    rewrite /run_step/=; case: look =>[|a0 r0 C0]//.
    case C0l': C0=>[[Ty0 L0]|]//; case: ifP=>//.
    move=>/andP-[_ /eqP-H]; move: H C0l'=><- C0l' {a0 r0 Ty0}.
    move: COND; rewrite orbC; case: a'=>//= NEQ'.
    - rewrite -runnable_upd //; case: P=>[E Q]/=.
      apply/runnable_next_queue => r/=.
      rewrite /enq/=; case: Q.[? _] =>[W|].
      + rewrite /deq fnd_set xpair_eqE andbC (negPf NEQ') /andb.
        by case: Q.[? _] =>[[|V [|V' W']]|]/=.
      + rewrite /deq fnd_set xpair_eqE andbC (negPf NEQ') /andb.
        by case: Q.[? _] =>[[|V [|V' W']]|]/=.
    - case DEQ: deq=>[[[l0 Ty0] Q']|]//=; last by rewrite -runnable_upd//.
      rewrite -runnable_upd//.
      apply: runnable_next_queue=> r.
      move: DEQ; rewrite /deq/=.
      case EQ: P.2.[? _] => [[|V [|V' W]]|]//= [_ <-] {Q'}.
      * rewrite fnd_rem1 xpair_eqE negb_and orbC (negPf NEQ) /orb/negb.
        by case: P.2.[? _] =>[[|V0 [|V1 W0]]|]/=.
      * rewrite fnd_set xpair_eqE andbC (negPf NEQ) /andb.
        by case: P.2.[? _] =>[[|V0 [|V1 W0]]|]/=.
  Qed.

  Lemma IProj_unr p CG L:
    IProj p (ig_end CG) L -> IProj p (rg_unr CG) L.
  Proof.
    move=>/IProj_end_inv; case: CG.
    + elim/Project_inv=>// G0 -> _ pof {G0 L}.
      by constructor; apply/paco2_fold; constructor.
    + move=>F T C /=; set CC := fun l=>_.
      have DOM_CC: same_dom C CC.
      { move=> l Ty; split; move=>[G E1];
          first (by exists (ig_end G); rewrite /CC E1).
        by move: E1; rewrite /CC; case: (C l)=>[[Ty' iG]|//] [->_]; exists iG.
      }
      case: (boolP (p == F))=>[/eqP->|pF]; [|case: (boolP (p == T))=>[/eqP->|pT]].
      - elim/Project_inv=>// .
        admit.
        admit.
      move=>/cProj_send_inv-[FT [Cl [-> [DOM PRJ]]]].
        constructor=>//; first by move=> l Ty; rewrite -DOM_CC.
        move=> L0 Ty G L' CC_L0 Cl_L0; move: CC_L0; rewrite /CC.
        move: (DOM L0 Ty)=>[_ /(_ (ex_intro _ _ Cl_L0))-[CG C_L0]].
        rewrite C_L0 =>[[<-]]; constructor.
        by move: PRJ; move=>/(_ L0 Ty CG L' C_L0 Cl_L0)=>[[PRJ|//]].
      - move=>/cProj_recv_inv-[FT [Cl [-> [DOM PRJ]]]].
        move: FT; rewrite eq_sym=>FT.
        constructor=>//; first by move=> l Ty; rewrite -DOM_CC.
        move=> L0 Ty G L' CC_L0 Cl_L0; move: CC_L0; rewrite /CC.
        move: (DOM L0 Ty)=>[_ /(_ (ex_intro _ _ Cl_L0))-[CG C_L0]].
        rewrite C_L0 =>[[<-]]; constructor.
        by move: PRJ; move=>/(_ L0 Ty CG L' C_L0 Cl_L0)=>[[PRJ|//]].
      - move=>/cProj_mrg_inv/(_ pF pT)-[FT [lC [DOM [PRJ MRG]]]].
        have /same_dom_trans/(_ DOM)-DOM_CC':
          same_dom CC C by move: DOM_CC=>/same_dom_sym.
        apply: iprj_mrg=>// l Ty G L' CC_l lC_l.
        move: CC_l; rewrite /CC; case C_l: (C l)=>[[Ty' CG]|//] H.
        move: H C_l=>[-><-] C_l {Ty'}; constructor.
        by move: PRJ; move=>/(_ l Ty CG L' C_l lC_l)=>[[PRJ|//]].
  Qed.

  Lemma QProj_unr CG Q :
    qProject (ig_end CG) Q -> qProject (rg_unr CG) Q.
  Proof.
    move=>/qProject_end_inv=>->.
    case: CG=>//=; first by constructor.
    move=> F T C; constructor; last by apply/not_fnd.
    move=>l Ty G; case: (C l)=>//[[Ty' G']]-[_ <-].
    by apply: qprj_end.
  Qed.

  Lemma local_runnable G P A G' :
    step A G G' -> Projection G P -> runnable A P.
  Proof.
  move=> ST PRJ.
  (* case: P => [E Q] ST PART [/=EPrj QPrj]. *)
  elim: ST =>
    [ L F T C Ty G'' C_L
    | L F T C Ty G'' C_L
    | {}A l F T C0 C1 AF AT NE DOM_C STEP_C Ih
    | {}A l F T C0 C1 AT DOM_C STEP_C Ih
    | a CG G0 ST_G0 Ih
    ] /= in P PRJ *.
  - rewrite /runnable/=.
    move: (PRJ.1 F) => IProj_F.
    move: (IProj_send1_inv IProj_F)=>[_ [lC [LF_msg [/(_ L Ty)-[DOM _] PRJ_C]]]].
    move: (DOM (ex_intro _ _ C_L)) => [L' lC_L].
    by rewrite LF_msg lC_L !eq_refl /=.
  - rewrite /runnable/=.
    move: (PRJ.1 T) => IProj_F.
    move: (IProj_recv_inv IProj_F)=>[_ [lC [LF_msg [/(_ L Ty)-[DOM _] PRJ_C]]]].
    move: (DOM (ex_intro _ _ C_L)) => [L' lC_L].
    move: (qProject_Some_inv PRJ.2) => [Ty' [{}G [Q' [C_L' [/eqP-Q_FT _]]]]].
    rewrite LF_msg lC_L !eq_refl/= Q_FT.
    by move: C_L C_L'=>-> [->]; rewrite !eq_refl.
  - move: PRJ=>/Proj_None_next-PRJ.
    move: NE=>[Ty [G0 C0l]].
    rewrite (runnable_next (A' := mk_act l_send F T l Ty)) ?AF ?AT//.
    rewrite (runnable_next (A' := mk_act l_recv T F l Ty)) ?AF ?AT//.
    move: PRJ=>/(_ _ _ _ C0l)-PRJ.
    move: (DOM_C l Ty)=>[/(_ (ex_intro _ _ C0l))-[G1 C1l] _].
    by apply: (Ih _ _ _ _ C0l C1l _ PRJ).
  - move: PRJ.2=>/qProject_Some_inv-[Ty [G0 [Q' [C0l [DEQ QPrj]]]]].
    move: PRJ=>/Proj_Some_next-PRJ.
    move: Ih=>[_ [Ty' [G1 [G2 [C0l' [C1l [STEP Ih]]]]]]].
    move: C0l' C1l STEP Ih; rewrite C0l => [[<-<-] C1l STEP Ih].
    move: (PRJ Ty G0 C0l)=>{}PRJ.
    rewrite (runnable_next (A':=mk_act l_recv T F l Ty)) ?orbT //=.
    by apply: (Ih _ PRJ).
  - apply: Ih.
    move: PRJ=>[ePRJ qPRJ]; split.
    + move: ePRJ; rewrite /eProject=>[PRJ].
      move=>p; move: (PRJ p)=>IPRJ.
      by apply/IProj_unr.
    + by apply/QProj_unr.
  Qed.

  Lemma look_same E F L : look E.[F <- L] F = L.
  Proof. by rewrite /look fnd_set eq_refl. Qed.

  Lemma Projection_send C l Ty G :
    C l = Some (Ty, G) ->
    forall F T P,
      Projection (ig_msg None F T C) P ->
      Projection (ig_msg (Some l) F T C) (run_step (mk_act l_send F T l Ty) P).
  Proof.
    move=>Cl F T P PRJ.
    move: (IProj_send1_inv (PRJ.1 F))=>[FT] [lCF] [EF] [DOMF] ALLF.
    move: (IProj_recv_inv (PRJ.1 T))=>[_] [lCT] [ET] [DOMT] ALLT.
    move: (dom DOMF Cl) (dom DOMT Cl) => [LF lCFl] [LT lCTl].
    rewrite /run_step/= EF lCFl !eq_refl/=.
    split.
    - move=>p; case: (boolP (p == F))=>[/eqP->{p}|];
      [|case: (boolP (p == T))=>[/eqP->{p} _|pT pF]].
      + by apply: (iprj_send2 FT FT DOMF ALLF); rewrite look_same; apply/lCFl.
      + rewrite look_comm //= ET.
        by apply: (iprj_recv _ _ DOMT ALLT); rewrite eq_sym.
      + rewrite look_comm //=; last by rewrite eq_sym.
        move: (IProj_mrg_inv (PRJ.1 p) pF pT)=>[_] [lCp] [DOMp] [ALLp] MRGp.
        move: (dom DOMp Cl) => [Lp lCpl].
        by apply/(EqL_IProj _ (MRGp _ _ _ lCpl))/(iprj_send2 pT FT DOMp ALLp lCpl).
    - move: (qProject_None_inv PRJ.2)=>[PFT] /(_ _ _ _ Cl)-QPRJ.
      apply: (qprj_some Cl _ QPRJ).
      rewrite /deq/enq/= PFT fnd_set eq_refl/= remf1_set eq_refl remf1_id //.
      by rewrite -fndSome PFT.
  Qed.

  Lemma Projection_recv C l Ty G :
    C l = Some (Ty, G) ->
    forall F T P,
      Projection (ig_msg (Some l) F T C) P ->
      Projection G (run_step (mk_act l_recv T F l Ty) P).
  Proof.
    move=>Cl F T P PRJ.
    move: (qProject_Some_inv PRJ.2)=>[TyQ] [GQ] [Q'].
    rewrite Cl=> [][] [<-<-] [/eqP-DEQ] QPRJ {TyQ GQ}.
    move: (IProj_recv_inv (PRJ.1 T))=>[FT] [lCT] [ET] [DOMT] ALLT.
    move: (IProj_send2_inv (PRJ.1 F) FT)=>[_] [lCF] [Ty'] [EF] [DOMF] ALLF.
    move: (dom DOMF Cl) (dom DOMT Cl) => [LF lCFl] [LT lCTl].
    move: lCFl; rewrite EF=>H; move: H EF=>[-> _] lCFl.
    rewrite /run_step/= ET lCTl !eq_refl/= DEQ.
    split=>//.
    move=>p; case: (boolP (p == F))=>[/eqP->{p}|];
             [|case: (boolP (p == T))=>[/eqP->{p} _|pT pF]].
    - rewrite look_comm; last by rewrite eq_sym.
      by apply: (ALLF _ _ _ _ Cl lCFl).
    - by rewrite look_same; apply: (ALLT _ _ _ _ Cl lCTl).
    - move: (IProj_send2_inv (PRJ.1 p) pT)=>[_] [lCp] [{}Ty'] [lCpl] [DOMp] ALLp.
      move: (dom DOMp Cl)=>[L'].
      rewrite lCpl=>[[ETy']] _ {L'}; move: ETy' lCpl=>-> lCpl.
      rewrite look_comm //; last by rewrite eq_sym.
      by apply/(ALLp _ _ _ _ Cl lCpl).
  Qed.

  Lemma do_actC E0 E1 E2 A1 A2 :
    subject A1 != subject A2 ->
    do_act E0 A1 = Some E1 ->
    do_act E0 A2 = Some E2 ->
    exists E3, do_act E1 A2 = Some E3 /\ do_act E2 A1 = Some E3.
  Proof.
    case: A1=>[a1 F1 T1 l1 Ty1]; case: A2=>[a2 F2 T2 l2 Ty2]/= FF.
    case E0F1: (look E0 F1) =>[|a3 q3 C3]//;
    case E0F2: (look E0 F2) =>[|a4 q4 C4]//.
    case C3l1: (C3 l1) => [[Ty3 L3]|]//; case: ifP=>// EQ [<-].
    case C4l2: (C4 l2) => [[Ty4 L4]|]//; case: ifP=>// EQ' [<-].
    rewrite /look !fnd_set eq_sym (negPf FF).
    move: E0F1; rewrite /look; case: E0.[? _] =>// L0->.
    move: E0F2; rewrite /look; case: E0.[? _] =>// {}L0->.
    rewrite C4l2 EQ' C3l1 EQ.
    rewrite setfC eq_sym (negPf FF).
    by exists (E0.[F2 <- L4]).[F1 <- L3].
  Qed.

  Lemma do_act_none E0 E1 A1 A2 :
    subject A1 != subject A2 ->
    do_act E0 A1 = Some E1 ->
    do_act E0 A2 = None ->
    do_act E1 A2 = None.
  Proof.
    case: A1=>[a1 F1 T1 l1 Ty1]; case: A2=>[a2 F2 T2 l2 Ty2]/= FF.
    case E0F1: (look E0 F1)=>[|a3 q3 C3]//.
    case C3l1: (C3 l1) => [[Ty3 L3]|]//; case: ifP=>// EQ [<-].
    case E0F2: (look E0 F2)=>[|a4 q4 C4]//.
    - rewrite /look fnd_set eq_sym (negPf FF).
      by move: E0F2; rewrite /look; case: (E0.[? F2])=>// L->.
    - case C4l2: (C4 l2) => [[Ty4 L4]|]//.
      + case: ifP=>// EQ0.
        move: E0F2; rewrite /look fnd_set eq_sym (negPf FF).
        by case: (E0.[? F2])=>//L'->; rewrite C4l2 EQ0.
      + move: E0F2; rewrite /look fnd_set eq_sym (negPf FF).
        by case: (E0.[? F2])=>//L'->; rewrite C4l2.
  Qed.

  Lemma enqC k k' (NEQ : k != k') Q v v' :
    enq (enq Q k v) k' v' = enq (enq Q k' v') k v.
  Proof.
    by rewrite /enq; case Qk: Q.[? k] => [W|];
       rewrite fnd_set eq_sym (negPf NEQ); case: Q.[? k'] =>[W'|];
       rewrite fnd_set (negPf NEQ) Qk //= setfC eq_sym (negPf NEQ).
  Qed.

  Lemma runnable_recv_deq F T l Ty P :
    runnable (mk_act l_recv F T l Ty) P ->
    exists Q W, deq P.2 (T, F) = Some ((l, Ty), Q) /\
              P.2.[? (T, F)] = Some ((l, Ty) :: W) /\
              forall k, k != (T, F) -> Q.[? k] = P.2.[? k].
  Proof.
    rewrite /runnable/=.
    case PF: (look P.1 F) =>[|a r C]//; case Cl: (C l) => [[Ty' L']|]//.
    case: ifP=>// COND; case DEQ: deq =>[[[l'] Ty'' Q]|]// /andP-[E1 E2].
    move:E1 E2 DEQ=>/eqP<-/eqP<-.
    rewrite /deq;case PTF: P.2.[? (T, F)] =>[[|[l0 Ty0] [|V' W]]|]//=[<-<-<-].
    - exists P.2.[~ (T, F)], [::]; do ! split=>//.
      by move=> k NEQ; rewrite fnd_rem1 NEQ.
    - exists P.2.[(T, F) <- V' :: W], (V'::W); do ! split=>//.
      by move=> k NEQ; rewrite fnd_set (negPf NEQ).
  Qed.

  Lemma deq_enq_neqC k k' (NEQ : k != k') v Q :
    deq (enq Q k v) k' =
    match deq Q k' with
    | Some (v', Q') => Some (v', enq Q' k v)
    | None => None
    end.
  Proof.
    by rewrite /deq/enq; (have NEQ': (k' != k) by (move: NEQ; rewrite eq_sym));
       case Qk': Q.[? k'] =>[[|v0 [|v1 w0] ]|]//=; case Qk: Q.[? k] =>[W|];
       rewrite fnd_set eq_sym (negPf NEQ) Qk' //= ?fnd_rem1 ?fnd_set (negPf NEQ)
               //= Qk ?remf1_set //= ?(negPf NEQ') //= setfC (negPf NEQ').
  Qed.

  Lemma deq_enq_sameC Q k' v' Q' :
    deq Q k' = Some (v', Q') ->
    forall k v, deq (enq Q k v) k' = Some (v', enq Q' k v).
  Proof.
    rewrite /deq; case Qk': Q.[? k'] => [[|V0 [|V0' W0]]|]//= [<-<-] {v' Q'} k v.
    - rewrite /enq; case Qk: Q.[? k] => [W|]//=; rewrite fnd_set;
      move: Qk' Qk; case: ifP=>[/eqP->|neq] Qk'; rewrite Qk'//=.
      + move=> [<-]/=; rewrite fnd_rem1 eq_refl /=.
        by rewrite setfC eq_refl setf_rem1.
      + by move=> Qk; rewrite fnd_rem1 eq_sym neq /= Qk remf1_set neq.
      + by move=> Qk; rewrite fnd_rem1 eq_sym neq /= Qk remf1_set neq.
    - rewrite /enq; case Qk: Q.[? k] => [W|]//=; rewrite fnd_set;
      move: Qk' Qk; case: ifP=>[/eqP->|neq] Qk'; rewrite Qk'//=.
      + move=> [<-]/=; rewrite fnd_set eq_refl /=.
        by rewrite setfC eq_refl setfC eq_refl.
      + by move=> Qk; rewrite fnd_set eq_sym neq /= Qk setfC neq.
      + by move=> Qk; rewrite fnd_set eq_sym neq /= Qk setfC neq.
  Qed.

  Lemma  deq_someC k0 k1 (NEQ : k0 != k1) Q v0 v1 Q0 Q1 :
    deq Q k0 = Some (v0, Q0) ->
    deq Q k1 = Some (v1, Q1) ->
    exists Q2, deq Q0 k1 = Some (v1, Q2) /\ deq Q1 k0 = Some (v0, Q2).
  Proof.
    rewrite /deq.
    case Qk0: Q.[? k0] => [[|V0 [|V0' W0]]|]//=;
    case Qk1: Q.[? k1] => [[|V1 [|V1' W1]]|]//= [<-<-] [<-<-] {v0 v1}.
    - exists Q.[~ k0].[~ k1].
      rewrite fnd_rem1 eq_sym NEQ Qk1 /= fnd_rem1 NEQ Qk0 /=; split=>//.
      by rewrite !remf_comp fsetUC.
    - exists Q.[~ k0].[k1 <- V1' :: W1].
      rewrite fnd_rem1 eq_sym NEQ Qk1 /=; split=>//.
      by rewrite fnd_set (negPf NEQ) Qk0 /= remf1_set (negPf NEQ).
    - exists (Q.[k0 <- V0' :: W0]).[~ k1].
      rewrite fnd_set eq_sym (negPf NEQ) Qk1; split=>//.
      by rewrite fnd_rem1 NEQ Qk0 /= remf1_set eq_sym (negPf NEQ).
    - exists (Q.[k0 <- V0' :: W0]).[k1 <- V1' :: W1].
      rewrite !fnd_set eq_sym (negPf NEQ) Qk0 Qk1 /=; split=>//.
      by rewrite setfC (negPf NEQ).
  Qed.

  Lemma  deq_noneC k0 k1 (NEQ : k0 != k1) Q v0 Q0 :
    deq Q k0 = Some (v0, Q0) ->
    deq Q k1 = None ->
    deq Q0 k1 = None.
  Proof.
    rewrite [in deq Q k0]/deq.
    by case Qk0: Q.[? k0] =>[[|V [|V' W]]|]//= [_ <-];
       rewrite /deq; case Qk1: Q.[? k1] =>[[|V1 [|V2 W1]]|]//=_;
       rewrite ?fnd_rem1 ?fnd_set eq_sym (negPf NEQ)/= Qk1.
  Qed.


  Lemma deq_neqC k k' (NEQ : k != k') Q :
    match deq match deq Q k' with | Some (_, Q') => Q' | None => Q end k with
    | Some (_, Q') => Q'
    | None => match deq Q k' with | Some (_, Q') => Q' | None => Q end
    end =
    match deq match deq Q k with | Some (_, Q') => Q' | None => Q end k' with
    | Some (_, Q') => Q'
    | None => match deq Q k with | Some (_, Q') => Q' | None => Q end
    end.
  Proof.
    case Qk': (deq Q k')=>[[v' Q']|];
      case Qk: (deq Q k)=>[[v Q'']|]; rewrite ?Qk' //.
    - by move: (deq_someC NEQ Qk Qk')=>[Q2] [->->].
    - by rewrite (deq_noneC _ Qk' Qk) // eq_sym.
    - by rewrite (deq_noneC NEQ Qk Qk').
  Qed.

  Lemma do_queueC A A' P :
    subject A != subject A' ->
    (subject A != object A') || (act_ty A' == l_recv) && runnable A' P ->
    do_queue (do_queue P.2 A') A = do_queue (do_queue P.2 A) A'.
  Proof.
    case: A=>[[] F T l Ty]; case: A'=>[[] F' T' l' Ty']//=.
    - by rewrite orbC/==> FF FT; rewrite enqC // xpair_eqE eq_sym negb_and FF.
    - move=> FF /orP-[FT|/runnable_recv_deq-[Q] [W] [DEQ] [LOOK] Q_EQ].
      + by rewrite deq_enq_neqC ?xpair_eqE ?negb_and ?FT //; case: deq=>[[]|].
      + by rewrite DEQ (deq_enq_sameC DEQ).
    - move=> FF; rewrite orbC eq_sym=>/= FT.
      by rewrite deq_enq_neqC ?xpair_eqE ?negb_and ?FT ?orbT//;case: deq=>[[]|].
    - by move=> FF _; apply: deq_neqC; rewrite xpair_eqE negb_and orbC FF.
  Qed.

  Lemma run_stepC A A' P :
    subject A != subject A' ->
    (subject A != object A') || ((act_ty A' == l_recv) && runnable A' P) ->
    run_step A (run_step A' P) = run_step A' (run_step A P).
  Proof.
    rewrite /run_step;
    case PA': (do_act P.lbl A')=>[E'|]/=; case PA: (do_act P.1 A)=>[E|]//=;
    rewrite ?PA' ?PA // => SUBJ.
    - move: (do_actC SUBJ PA PA')=> [E3] [->->] COND.
      by rewrite do_queueC.
    - by move: SUBJ; rewrite eq_sym=>SUBJ; rewrite (do_act_none SUBJ PA' PA).
    - by rewrite (do_act_none SUBJ PA PA').
  Qed.

  Lemma Projection_runnable l Ty G F T C P :
    C l = Some (Ty, G) ->
    Projection (ig_msg (Some l) F T C) P ->
    runnable (mk_act l_recv T F l Ty) P.
  Proof.
    move=> Cl [EPROJ QPROJ].
    move: EPROJ; rewrite /eProject=>/(_ T)-PRJ.
    move: PRJ=>/IProj_recv_inv=>[[FT] [lC] [E_lT] [DOM] PRJ].
    move: QPROJ=>/qProject_Some_inv=>[] [Ty'] [G0] [Q'] [Cl'] [DEQ] QPRJ.
    move: Cl' DEQ QPRJ; rewrite Cl =>[] [<-<-] /eqP-DEQ QPRJ {Ty' G0}.
    move: (DOM l Ty)=>[/(_ (ex_intro _ _ Cl))-[L' lCl] _].
    by rewrite /runnable/= E_lT lCl !eq_refl /= DEQ !eq_refl.
  Qed.

  Lemma Projection_unr G P :
    Projection (ig_end G) P -> Projection (rg_unr G) P.
  Proof.
    move=>[EPRJ QPRJ]; split.
    - move=>p; move: (EPRJ p)=>{}EPRJ.
      by apply: IProj_unr.
    - by apply: QProj_unr.
  Qed.


  Definition PAll (C : lbl /-> mty * ig_ty) P
    := forall l Ty G, C l = Some (Ty, G) -> Projection G (P l Ty).

  Definition send_recv F T L Ty P :=
    run_step (mk_act l_recv T F L Ty) (run_step (mk_act l_send F T L Ty) P).

  Lemma look_act A P F :
    subject A != F -> look (run_step A P).1 F = look P.1 F.
  Proof.
    case A=>[a p q l Ty]; rewrite /run_step/do_act/=.
    case: (look P.1 p) =>// a' r' C'; case: (C' l)=> [[Ty' L]|]//.
    by case: ifP=>// _ pF; rewrite look_comm.
  Qed.

  Lemma queue_act A F T P :
    (subject A != F) ->
    (subject A != T) ->
    ((run_step A P).2).[? (F, T)] = P.2.[? (F, T)].
  Proof.
    case A=>[a p q l Ty]; rewrite /run_step/do_act/=.
    case: (look P.1 p) =>// a' r' C'; case: (C' l)=> [[Ty' L]|]//.
    case: ifP=>// _ pF pT; case: a=>//; rewrite /enq/deq.
    - by case: P.2.[? _] =>[a|]; rewrite fnd_set xpair_eqE eq_sym (negPf pF).
    - case: P.2.[? _] =>[[|V0 [|V1 W]]|]//.
      + by rewrite fnd_rem1 xpair_eqE negb_and orbC eq_sym  (negPf pT).
      + by rewrite fnd_set xpair_eqE andbC eq_sym (negPf pT).
  Qed.

  Lemma dom_none A B (C0 : lbl /-> mty * A) (C1 : lbl /-> mty * B)
    : same_dom C0 C1 -> forall l, C0 l = None -> C1 l = None.
  Proof.
    move=>DOM l Cl; case C1l: (C1 l)=>[[Ty] b|]//.
    by move: (dom' DOM C1l)=>[G0]; rewrite Cl.
  Qed.

  Lemma dom_none' A B (C0 : lbl /-> mty * A) (C1 : lbl /-> mty * B)
    : same_dom C0 C1 -> forall l, C1 l = None -> C0 l = None.
  Proof. by rewrite same_dom_sym; apply/dom_none. Qed.

  Definition buildC (C : lbl /-> mty * ig_ty) E p :=
    fun l => match C l with
             | Some (Ty, _) => Some (Ty, look E p)
             | None => None
             end.

  Lemma dom_buildC C E p : same_dom C (buildC C E p).
  Proof.
    move=>l Ty; rewrite/buildC;case EQ: (C l)=>[[Ty' G]|]; split=>[][G']//[->_].
    - by exists (look E p).
    - by exists G.
  Qed.

  Lemma mrg_buildC C E p : Merge (buildC C E p) (look E p).
  Proof.
    move=> l Ty L'; rewrite /buildC; case: (C l)=>[[Ty' G]|]// [_->].
    by apply: EqL_refl.
  Qed.
  Arguments mrg_buildC C E p : clear implicits.

  Lemma proj_all P C Cl :
    same_dom C Cl ->
    PAll C P ->
    forall p,
      (forall l Ty L, Cl l = Some (Ty, L) -> look (P l Ty).1 p = L) ->
      R_all (IProj p) C Cl.
  Proof.
    move=> DOM All p H l Ty G L /All-[ePRJ qPRJ] Cll.
    by move: (H l Ty L Cll) (ePRJ p) =>->.
  Qed.

  Lemma case_part (p F T : role) : p = F \/ p = T \/ (p != F /\ p != T).
  Proof.
    case: (boolP (p == F))=>[/eqP-pF|pF]; [by left|right].
    by case: (boolP (p == T))=>[/eqP-pT|pT]; [by left|right].
  Qed.

  Lemma Proj_send_undo F lCF T lCT C P l Ty G1 :
    F != T ->
    C l = Some (Ty, G1) ->
    same_dom C lCF ->
    same_dom C lCT ->
    look P.1 F = rl_msg l_send T lCF ->
    look P.1 T = rl_msg l_recv F lCT ->
    PAll C (fun L : lbl => (send_recv F T L)^~ P) ->
    (P.2).[? (F, T)] = None ->
    Projection (ig_msg None F T C) P.
  Proof.
    move=> FT Cl DOMF DOMT EF ET PRJ QPRJ.
    have DOM: same_dom lCF lCT by move: DOMT; apply/same_dom_trans/same_dom_sym.
    split.
    - move: (dom_buildC C P.1) (mrg_buildC C P.1)=> DOMp MRGp.
      move=> p; move: (case_part p F T)=>[->|[->|[pF pT]]].
      + rewrite EF; constructor=>//.
        apply/(proj_all DOMF PRJ)=>l0 Ty0 L lCF0.
        rewrite /send_recv look_act//=; last by rewrite eq_sym.
        by rewrite /run_step/= EF lCF0 !eq_refl /= look_same.
      + rewrite ET; constructor=>//; first by rewrite eq_sym.
        apply/(proj_all DOMT PRJ)=>l0 Ty0 L lCT0; rewrite /send_recv.
        move: (dom' DOM lCT0)=>[L'] lCF0.
        rewrite /run_step/= EF lCF0 !eq_refl /= look_comm // ET lCT0 !eq_refl/=.
        by rewrite look_same.
      + apply: (iprj_mrg FT pF pT (DOMp p)); last by apply/MRGp.
        apply/(proj_all (DOMp p) PRJ)=>l0 Ty0 L lCp0.
        rewrite /send_recv look_act //=; last by rewrite eq_sym.
        rewrite look_act //=; last by rewrite eq_sym.
        by move: lCp0; rewrite /buildC; case: (C l0)=>[[Ty1 _] []|].
    - constructor=>// l0 Ty0 G0 /PRJ-[_].
      rewrite /send_recv [in run_step (mk_act l_send _ _ _ _) _]/run_step/=.
      rewrite EF; case lCF0: (lCF l0)=>[[Ty1 L0]|].
      + move: (dom DOM lCF0)=>[LT] lCT0.
        rewrite !eq_refl/=; case: ifP=>E.
        * rewrite /enq QPRJ/run_step/= look_comm // ET lCT0 E !eq_refl/=.
          rewrite /deq fnd_set !eq_refl /= remf1_set eq_refl remf1_id //.
          by rewrite -fndSome QPRJ.
        * by rewrite /run_step/= ET !eq_refl /= lCT0 E.
      + by move: (dom_none DOM lCF0)=>lCT0; rewrite /run_step/= ET lCT0.
  Qed.

  Lemma deq_act A F T P l Tyl Q' :
    subject A != T ->
    deq P.2 (F, T) = Some (l, Tyl, Q') ->
    deq (run_step A P).2 (F, T) = Some (l, Tyl, (run_step A (P.1, Q')).2).
  Proof.
    case: A=>[a p q l' Ty']; rewrite /run_step/=.
    case: look=>[|a0 r0 C0]//.
    case: (C0 l')=>// [[Ty1 L1]].
    case: ifP=>//COND; case: a COND=>//= COND pT DEQ.
    - by apply: (deq_enq_sameC DEQ).
    - move: DEQ; rewrite /deq/=.
      case EQ: (P.2.[? (F, T)]) =>[[|V0 W]|]//.
      case EQ': (P.2.[? (q, p)])=>[[|V1 W']|]//.
      + rewrite EQ.
        case: ifP EQ=>[/eqP->|WEQ]; move=>PFT [<-] <-.
        * by rewrite fnd_rem1 xpair_eqE negb_and orbC pT /= EQ'.
        * by rewrite fnd_set xpair_eqE andbC (negPf pT) /= EQ'.
      + case: ifP EQ=>[/eqP-EQW|WEQ]  PFT [<-<-]; case:ifP=>EQ//.
        * rewrite fnd_rem1 xpair_eqE negb_and orbC eq_sym pT PFT /orb EQW.
          rewrite eq_refl fnd_rem1 xpair_eqE negb_and pT orbT EQ' EQ /orb.
          by rewrite !remf_comp fsetUC.
        * rewrite fnd_set xpair_eqE andbC eq_sym (negPf pT) PFT /andb EQW.
          rewrite fnd_rem1 xpair_eqE negb_and pT orbT EQ' EQ remf1_set.
          by rewrite xpair_eqE andbC eq_sym (negPf pT).
        * rewrite fnd_rem1 xpair_eqE negb_and orbC eq_sym pT /orb PFT.
          rewrite fnd_set xpair_eqE (negPf pT) andbC /andb EQ' EQ WEQ.
          by rewrite remf1_set xpair_eqE (negPf pT) andbC.
        * rewrite fnd_set xpair_eqE andbC eq_sym (negPf pT) /andb PFT WEQ.
          rewrite fnd_set xpair_eqE andbC (negPf pT) /andb EQ' EQ.
          by rewrite setfC xpair_eqE andbC eq_sym (negPf pT).
      + case: ifP EQ=>[/eqP->|WEQ] PFT [<-<-]; rewrite PFT.
        * by rewrite fnd_rem1 xpair_eqE negb_and pT orbC /= EQ'.
        * by rewrite WEQ fnd_set xpair_eqE andbC (negPf pT)/= EQ'.
  Qed.

  (* FIXME: fix statement by adding the fact that continuations != l do not change (and therefore we know
     their projection)
  *)

  Definition R_all_except (l' : lbl) (R : ig_ty -> rl_ty -> Prop)
             (C : lbl /-> mty * ig_ty) (lC : lbl /-> mty * rl_ty) :=
    forall l Ty G L,
      l' != l -> C l = Some (Ty, G) -> lC l = Some (Ty, L) -> R G L.

  Definition updC (l : lbl) (Ty : mty) C E p l' :=
    if l == l' then
      Some (Ty, look E p)
    else
      C l'.

  Lemma dom_updC l Ty C E p L' :
    C l = Some (Ty, L') ->
    same_dom C (updC l Ty C E p).
  Proof.
    move=>Cl l1 Ty1;split=>[][G]; rewrite/updC; case: ifP=>EQ.
    + by move: EQ=>/eqP<-; rewrite Cl=>[][<- _]; exists (look E p).
    + by move=>->; exists G.
    + by move: EQ=>/eqP<-; move=>[<-]; exists L'.
    + by move=>->; exists G.
  Qed.

  Lemma Proj_recv_undo l F T C lCT Ty P G Q' :
    F != T ->
    C l = Some (Ty, G) ->
    look P.lbl T = rl_msg l_recv F lCT ->
    same_dom C lCT ->
    R_all_except l (IProj T) C lCT ->
    deq P.2 (F, T) = Some (l, Ty, Q') ->
    (forall p, exists lC, same_dom C lC /\ R_all_except l (IProj p) C lC)  ->
    Projection G (run_step (mk_act l_recv T F l Ty) P) ->
    Projection (ig_msg (Some l) F T C) P.
  Proof.
    move=> FT Cl ET DOM ALLT PFT PRJ0 PRJ1; split.
    - move=>p; case: (boolP (p == T))=>[/eqP->|pT].
      + move: FT; rewrite eq_sym ET=>TF.
        apply (iprj_recv (Some l) TF)=>// l0 Ty0 G0 L0 Cl0 lCT0.
        move: (PRJ1.1 T); rewrite /run_step/= ET.
        move: (dom DOM Cl)=>[LT] lCTl; rewrite lCTl !eq_refl /= look_same=>PRJ.
        case: (boolP (l == l0)) => [/eqP|]ll0.
        * by move: ll0 Cl0 lCT0=><-; rewrite Cl lCTl =>[][<-]<-[<-] //.
        * by apply/(ALLT _ _ _ _ ll0 Cl0).
      + move: (PRJ0 p)=>[lCp] [DOMp] ALLp.
        move: (dom DOMp Cl) => [Lp] lCpl.
        move: (dom_updC P.1 p lCpl)=>DOMp'.
        move: (same_dom_trans DOMp DOMp')=>{}DOMp'.
        apply: (iprj_send2 pT FT DOMp'); last by rewrite /updC eq_refl.
        move=> l0 Ty0 G0 G'; rewrite /updC.
        case: (boolP (l == l0))=>[/eqP<-|NEQ].
        * move=> Cl0 [EQ_Ty] <-; move: Cl0; rewrite Cl=>[][_ <-].
          move: (PRJ1.1 p); rewrite /run_step/= ET.
          move: (dom DOM Cl)=>[LT] lCTl; rewrite lCTl !eq_refl /= look_comm //.
          by rewrite eq_sym.
        * by apply/(ALLp l0 Ty0 G0 G' NEQ).
    - move: PFT=>/eqP-PFT; apply: (qprj_some Cl PFT).
      move: PFT=>/eqP-PFT; move: (dom DOM Cl)=>[L] lCtl.
      by move: PRJ1.2; rewrite /run_step/= ET lCtl !eq_refl/= PFT.
  Qed.

  (* Not quite right yet *)
  Lemma  proj_same l C0 C1 F T E :
    same_dom C0 C1 ->
    (forall l' K, l != l' -> C0 l' = Some K <-> C1 l' = Some K) ->
    eProject (ig_msg (Some l) F T C0) E ->
    forall p, exists lC,
        same_dom C1 lC /\
        forall l' Ty' G' L',
          l != l' ->
          C1 l' = Some (Ty', G') ->
          lC l' = Some (Ty', L') ->
          IProj p G' L'.
  Proof.
    move=> DOM SAME_C PRJ p.
    move: (IProj_recv_inv (PRJ T))=>[FT] [lC] [ET] [DOMT] ALLC.
    move _: DOM => DOM'; move:DOM'=>/same_dom_sym/same_dom_trans/(_ DOMT)-{}DOMT.
    case: (boolP (p == T))=>[/eqP->|NEQ].
    - exists lC; split=>// l' Ty' G' L' NE C1l lCl.
      by apply/(ALLC _ _ _ _ _ lCl)/SAME_C.
    - move: (IProj_send2_inv (PRJ p) NEQ)=>[_] [lCp] [Typ] [lCpl] [DOMp] ALLp.
      move _: DOM => DOM'; move:DOM'=>/same_dom_sym/same_dom_trans/(_ DOMp)-{}DOMp.
      exists lCp; split=>// l' Ty' G' L' NE C1l lCl.
      by apply/(ALLp _ _ _ _ _ lCl)/SAME_C.
  Qed.

  Lemma runstep_proj G P : forall A G',
    step A G G' -> Projection G P -> Projection G' (run_step A P).
  Proof.
    move=> A G' ST PRJ; elim: ST=>
    [ l F T C Ty G0 Cl
    | l F T C Ty G0 Cl
    | {}A l F T C0 C1 aF aT NE DOM STEP Ih
    | {}A l F T C0 C1 aT DOM STEP Ih
    | {}A CG G0 STEP Ih
    ]/= in P PRJ *.
    - by apply: (Projection_send Cl).
    - by apply: (Projection_recv Cl).
    - move: (IProj_send1_inv (PRJ.1 F))=>[FT] [lCF] [EF] [DOMF] _.
      move: (IProj_recv_inv (PRJ.1 T))=>[_] [lCT] [ET] [DOMT] _.
      move: EF; rewrite -(look_act _ aF)=>{}EF.
      move: ET; rewrite -(look_act _ aT)=>{}ET.
      move _: DOM=>DOM1; move: DOM1=>/same_dom_sym-DOM1.
      move: (same_dom_trans DOM1 DOMF) (same_dom_trans DOM1 DOMT)=>{}DOMF {}DOMT.
      move: NE=>[Ty] [Gl] /(dom DOM)-[G1] C1l.
      move: PRJ.2=>/qProject_None_inv-[QPRJ] _.
      suff Ih': PAll C1 (fun L Ty => send_recv F T L Ty (run_step A P))
        by apply: (Proj_send_undo FT C1l DOMF DOMT) =>//; rewrite queue_act.
      move=>l0 Ty0 {}G1 {}C1l; move: (dom' DOM C1l)=>[G0 C0l].
      move: (Proj_None_next PRJ C0l)=>PRJ0; rewrite /send_recv.
      rewrite -(run_stepC (A:=A)) ?aT //= -(run_stepC (A:=A)) ?aF ?aT //=.
      by apply: Ih; [apply: C0l | apply: C1l |].
    - move: Ih=>[SAME_C] [Tyl] [G0] [G1] [C0l] [C1l] [STEP_G0_G1] Ih.
      move: (Projection_runnable C0l PRJ) => RUN.
      move: (IProj_recv_inv (PRJ.1 T))=>[FT] [lCT] [ET] [DOMT] PRJT.
      move: ET; rewrite -(look_act _ aT)=>{}ET.
      move _: DOM=> DOM1; move: DOM1=>/same_dom_sym-DOM1.
      move: (same_dom_trans DOM1 DOMT)=>{}DOMT.
      move: PRJ.2=>/qProject_Some_inv-[Ty] [G2] [Q'] [].
      rewrite C0l=>[][<-<-] [/eqP/(deq_act aT)-DEQ] _ {Ty G2}.
      move: (proj_same DOM SAME_C PRJ.1)=>PRJ_C1.
      move: (Proj_Some_next PRJ)=>/(_ _ _ C0l)/Ih.
      rewrite run_stepC ?RUN ?orbT // => {}Ih.
      apply: (Proj_recv_undo FT C1l ET DOMT _ DEQ PRJ_C1)=>//.
      move=>l0 Ty0 G2 L ll0 /(SAME_C _ _ ll0)-Cl0 lCT0.
      by apply/(PRJT _ _ _ _ Cl0).
    - by apply/Ih/Projection_unr.
  Qed.

  Theorem Project_step G P : forall A G',
    step A G G' ->
    Projection G P ->
    exists P', Projection G' P' /\ lstep A P P'.
  Proof.
  move=> A G' ST Prj; exists (run_step A P); split.
  - apply/(runstep_proj ST Prj).
  - apply/run_step_sound/(local_runnable ST Prj).
  Qed.


End TraceEquiv.
