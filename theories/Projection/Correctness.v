From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco1 paco2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.
Require Import MPST.Global.
Require Import MPST.Local.

Require Import MPST.Projection.IProject.
Require Import MPST.Projection.CProject.

Section Correctness.

Lemma partof_all_unroll G CG p L n :
  g_closed G ->
  GUnroll G CG -> project simple_merge G p == Some L ->
  depth_part n p G -> part_of_all p CG.
Proof.
  elim: n G CG L=>// n Ih [||G|F T C] //= CG L cG; rewrite -/prj_all.
  - case PRJ: project=>[L0|]//; move: PRJ=>/eqP-PRJ.
    case: ifP; first by move=>/(lbinds_depth _ PRJ)->.
    move=> NB /gunroll_unfold; elim/gunr_inv=>// _ IG CG0 GU [EQ1] EQ2 _ DP.
    move: EQ1 EQ2 GU DP=>//-> _ []//GU /(depthpart_open 0 (g_rec G))-DP.
    move: NB PRJ=>/eqP-NB /eqP-PRJ; move: (project_open NB cG PRJ)=>{}/eqP-P.
    by move: cG=>/gopen_closed/Ih/(_ GU P DP).
  - move=>/gunroll_unfold; elim/gunr_inv=>// _ F' T' C' CC DOM UA E1 _ {CG}.
    move: E1 DOM UA=>[->->->] DOM UA {F' T' C'}; rewrite -/(prj_all _ _).
    case PRJ: prj_all=>[Ks|]//; case: ifP=>// FT.
    case: ifP=>[/eqP<- _|pF]; first by constructor.
    case: ifP=>[/eqP<- _|pT]; first by constructor.
    move=>MRG; rewrite eq_sym pF eq_sym pT/= => DP.
    apply: pall_cont=>l Ty CG CCl.
    move: (dom' DOM CCl)=>[G'] Cl.
    move: (UA _ _ _ _ Cl CCl)=>[|//].
    move: (prj_all_find PRJ Cl)=>[L'][_]/eqP-{}PRJ GU.
    move: (find_member Cl)=>M.
    apply: (Ih _ _ _ _ GU PRJ).
    * by move: cG; rewrite /g_closed/= flatten_eq_nil=>/member_map/(_ _ M).
    * by move: DP =>/forallbP/forall_member/member_map/(_ _ M).
Qed.

Lemma partof_unroll G CG p :
  g_closed G ->
  guarded 0 G ->
  GUnroll G CG ->
  part_of p CG ->
  p \in participants G.
Proof.
  move=> cG gG GU PART.
  elim: PART=>[F T C| F T C|{}p F T C l G0 Ty Cl PART Ih] in G cG gG GU *.
  - apply: r_in_unroll_rec_depth; move: GU=>/(GUnroll_ind (rec_depth G)).
    move: (n_unroll (rec_depth G) G) (unroll_guarded cG gG)=>{cG gG}G NR GU.
    move: GU NR=>/gunroll_unfold; elim/gunr_inv =>// _;
      first by move=> IG _ _ _ _ /(_ IG); rewrite eq_refl.
    by move=> F' T' C' CG' _ _ _ [->] _ _ _; rewrite in_cons eq_refl.
  - apply: r_in_unroll_rec_depth; move: GU=>/(GUnroll_ind (rec_depth G)).
    move: (n_unroll (rec_depth G) G) (unroll_guarded cG gG)=>{cG gG}G NR GU.
    move: GU NR=>/gunroll_unfold; elim/gunr_inv =>// _;
      first by move=> IG _ _ _ _ /(_ IG); rewrite eq_refl.
    by move=> F' T' C' CG' _ _ _ [] _ <- _ _; rewrite in_cons orbC in_cons eq_refl.
  - apply: r_in_unroll_rec_depth; move: GU=>/(GUnroll_ind (rec_depth G)).
    move: (g_guarded_nunroll (rec_depth G) cG gG) (unroll_guarded cG gG).
    move: (n_unroll (rec_depth G) G) (g_closed_unroll (rec_depth G) cG).
    move=>{cG gG}G cG gG NR GU.
    move: GU NR cG gG =>/gunroll_unfold; elim/gunr_inv =>// _;
      first by move=> IG _ _ _ _ /(_ IG); rewrite eq_refl.
    move=> F' T' C' CG' DOM UA E1 E2 _ .
    rewrite /g_closed/==>/flatten_eq_nil/member_map-cG.
    move=>/forallbP/forall_member=>gG.
    move: E1 E2 cG gG DOM UA=>_ [->->->] cG gG DOM UA {G F' T' CG'}.
    suff: p \in flatten [seq participants K.2.2 | K <- C']
      by rewrite !in_cons=>->; rewrite orbC orbT.
    move: (dom' DOM Cl)=>[G FND]; move: (find_member FND)=>M.
    move: (UA _ _ _ _ FND Cl)=>[GU|//].
    apply/flatten_mapP; exists (l, (Ty, G)); first by apply/memberP.
    by apply/(Ih _ (cG _ M) (gG _ M) GU).
Qed.

Notation CIH4 X Y H1 H2 H3 H4 H5
  := (ex_intro (fun=>_) X
               (ex_intro (fun=>_) Y
                         (conj H1 (conj H2 (conj H3 (conj H4 H5)))))).
Lemma project_wf G p L CG :
  g_closed G ->
  guarded 0 G ->
  non_empty_cont G ->
  project simple_merge G p == Some L ->
  GUnroll G CG -> WF CG.
Proof.
  move=>H1 H2 NE H3 H4; move: (CIH4 L G H1 H2 NE H3 H4)=> {H1 H2 NE H3 H4 G L}.
  move: CG; apply/paco1_acc=>r _ /(_ _ (CIH4 _ _ _ _ _ _ _))-CIH.
  move=> CG [L] [G] [cG [gG [NE [PRJ GU]]]]; apply/paco1_fold.
  move: (unroll_guarded cG gG); move: PRJ=>/eqP-PRJ.
  move: (project_unroll (rec_depth G) cG PRJ)=>[n1][n2][L'][{}PRJ] _.
  move: GU=>/(GUnroll_ind (rec_depth G)); move: PRJ.
  move: gG=>/(g_guarded_nunroll (rec_depth G) cG).
  move: cG=>/(g_closed_unroll (rec_depth G)).
  move: NE=>/(ne_unr (rec_depth G)).
  move: (n_unroll (rec_depth G) G) => {}G; move: L'=>{}L {n1 n2}.
  case: G =>/=; rewrite -/prj_all.
  - by move=>_ _ _ _  /gunroll_unfold; elim/gunr_inv=>//; constructor.
  - by move=>v /=; rewrite /g_closed/=.
  - by move=>G _ _ _ _ _ /(_ G); rewrite eq_refl.
  - rewrite /g_closed; move=> F T C NE /= /flatten_eq_nil/member_map-cC.
    move=>/forallbP/forall_member-gG; rewrite -/(prj_all _ _).
    case PRJ: prj_all =>[L'|//]; move: PRJ=>/eqP-PRJ.
    case: ifP=>// FT _; move=>/gunroll_unfold.
    have CNE: C != [::] by case: C NE {cC gG PRJ}.
    have {}NE: all id [seq non_empty_cont K.2.2 | K <- C]
      by case: C NE {CNE cC gG PRJ}.
    move: NE=>/forallbP/forall_member/member_map-NE.
    elim/gunr_inv => // _ F' T' C' CC DOM UA E1 _ _ {CG}.
    move: E1 DOM UA=>[->->->] DOM UA {F' T' C'}; constructor; rewrite ?FT//.
    * move=> l Ty G CCl; right; move: (dom' DOM CCl)=>[G']FND.
      move: PRJ=>/eqP-PRJ; move: (prj_all_find PRJ FND)=>[L0][_]/eqP-{}PRJ.
      move: (UA _ _ _ _ FND CCl) (find_member FND)=>[GU|//] M.
        by apply (CIH _ _ _ (cC _ M) (gG _ M) (NE _ M) PRJ GU).
    * case: C CNE DOM {cC gG PRJ NE UA}=>//[][l [Ty G]] Ks _.
      have FND: find_cont ((l, (Ty, G)) :: Ks) l = Some (Ty, G)
        by rewrite/find_cont/extend eq_refl.
        by move=>DOM; move: (dom DOM FND)=> CCl; exists l, Ty.
Qed.

Lemma lunroll_merge (CL: rl_ty) (Ks: seq (lbl * (mty * l_ty)))
  : exists CCL,
      same_dom (find_cont Ks) CCL /\ simple_co_merge CCL CL.
Proof.
  set CCL := fun l =>
               match find_cont Ks l with
               | Some (Ty, _) => Some (Ty, CL)
               | None => None
               end.
  exists CCL; split.
  - move=> l Ty; split=>[][G]; rewrite /CCL/=.
    + by move=>->; exists CL.
    + by case: find_cont=>// [][Ty' G'][<-_]; exists G'.
  - rewrite /CCL=>l Ty L'; case: find_cont=>//[][Ty' G'][_]->.
    by apply/EqL_refl.
Qed.



(*NMC: the following should be the core synchronisation axiom
  for merge and co_merge. I stated it with the simple merge and co_merge for now,
  so that I can see whether the proof goes through.*)
(*NMC: TODO, check if l_precond hypothesis is needed.*)
Axiom merge_correct: forall Ks L CL,
    (forall K, member K Ks -> l_precond K.2.2) ->
    LUnroll L CL ->
  merge_all simple_merge [seq K.2.2 | K <- Ks] = Some L ->
  simple_co_merge (find_cont (map (fun K=> (K.1,(K.2.1, l_expand K.2.2)) ) Ks) ) CL(*l_expand L*).

Lemma project_nonrec (r0 : proj_rel ) r CL CG L G
      (CIH : forall cG cL iG iL,
          g_closed iG ->
          guarded 0 iG ->
          non_empty_cont iG ->
          project simple_merge iG r == Some iL ->
          GUnroll iG cG ->
          LUnroll iL cL ->
          r0 cG cL)
      (cG : g_closed G)
      (gG : guarded 0 G)
      (NE : non_empty_cont G)
      (nrG : forall G' : g_ty, G != g_rec G')
      (iPrj : project simple_merge G r = Some L)
      (GU : GUnroll G CG)
      (LU : LUnroll L CL)
  : paco2 (Proj_ simple_co_merge r) r0 CG CL.
Proof.
  move: (closed_not_var cG).
  case: (boolP (r \notin participants G)); [| rewrite negbK].
  - move=> PARTS nvG; move: iPrj=>/eqP-iPrj.
    move: (proj1 (project_parts cG iPrj) PARTS)=> endL.
    move: (lunroll_isend LU endL)=>->; apply/paco2_fold.
    constructor; first by move=>/(partof_unroll cG gG GU)-P'; move: P' PARTS=>->.
    by apply/(project_wf cG gG NE iPrj).
  - case: G cG gG NE nrG iPrj GU=>//;
            first by move=> GT _ _ _ /(_ GT); rewrite eq_refl.
    move=>FROM TO CONT; rewrite project_msg /g_closed/=.
    move=>/flatten_eq_nil/member_map-cG /forallbP/forall_member-gG.
    move=>/andP-[NE_C /forallbP/forall_member/member_map-NE] _ I_prj GU PARTS _.
    move: GU; move=>/gunroll_unfold.
    case E: _ _/ =>// [FROM' TO' CONT' CC DOM GU].
    move: E DOM GU=> [<-<-<-] {FROM' TO' CONT'} DOM GU.
    apply/paco2_fold; move: I_prj.
    case E: prj_all=>[KsL|]//; case:ifP=>// F_neq_T.
    case:ifP=>[F_r | F_ne_r].
    + move=>[EL]; move: EL LU=><- {L} /lu_unfold-LU.
      case EL: _ _/LU=>[||a p Ks C LD LU]//; move: EL LD LU=>[<-<-<-] LD LU {a p Ks}.
      move: (prjall_dom E)=>iDOM.
      move: F_r CIH E=>/eqP<- CIH E; apply/prj_send; first by apply/negPf.
      * by apply/(same_dom_trans
                    (same_dom_trans ((same_dom_sym _ _).1 DOM) iDOM)).
      * move=> l Ty G G' CCl Cl; right; move: (dom' DOM CCl)=>[iG FND].
        move: (GU _ _ _ _ FND CCl)=>[{}GU|//].
        move: (dom iDOM FND)=>[iL FND'].
        move: (LU _ _ _ _ FND' Cl)=>[{}LU|//].
        move: (prjall_fnd E FND FND')=>/eqP-PRJ.
        move: (find_member FND)=>M.
        by apply: (CIH _ _ _ _ (cG _ M) (gG _ M) (NE _ M) PRJ GU LU).
    + case:ifP=>[T_r | T_ne_r].
      * move=>[EL]; move: EL LU=><- {L} /lu_unfold-LU {F_ne_r}.
        case EL: _ _/LU=>[||a p Ks C DU LU]//; move: EL DU LU=>[<-<-<-] DU LU {a p Ks}.
        move: T_r CIH E=>/eqP<- CIH E.
        move: (prjall_dom E)=>iDOM.
        apply/prj_recv; first by rewrite eq_sym (F_neq_T).
        - by apply/(same_dom_trans
                      (same_dom_trans ((same_dom_sym _ _).1 DOM) iDOM)).
        - move=> l Ty G G' CCl Cl; right; move: (dom' DOM CCl)=>[iG FND].
          move: (GU _ _ _ _ FND CCl)=>[{}GU|//].
          move: (dom iDOM FND)=>[iL FND'].
          move: (LU _ _ _ _ FND' Cl)=>[{}LU|//].
          move: (prjall_fnd E FND FND')=>/eqP-PRJ.
          move: (find_member FND)=>M.
          by apply: (CIH _ _ _ _ (cG _ M) (gG _ M) (NE _ M) PRJ GU LU).
      * move=> MRG.
        (*have M: simple_merge L [seq K.2.2 | K <- KsL] = Some L
          by move: MRG=>{E}; case: KsL=>//=K Ks /eqP-M;
             move: (simple_merge_some M)=>E; move: E M=>->; rewrite eq_refl=>/eqP.
        move: (lunroll_merge CL KsL (*LU E M*))=>[CCL [DL cMRG]].*)
        move: F_ne_r T_ne_r; rewrite eq_sym=>F_ne_r; rewrite eq_sym=>T_ne_r.
        (*apply: prj_mrg ; rewrite ?F_ne_r ?T_ne_r ?F_neq_T//; last by apply:cMRG.*)
        apply: (@prj_mrg _ _ _ _ _ _
                         (find_cont (map (fun K=> (K.1,(K.2.1, l_expand K.2.2)) ) KsL) ));
          rewrite ?F_ne_r ?T_ne_r ?F_neq_T//.
        - case: CONT NE_C DOM {cG gG NE PARTS GU E}=>// K Ks _ DOM.
          case: K DOM=>[l [Ty G] DOM]/=.
          have: (find_cont ((l, (Ty, G)) :: Ks) l = Some (Ty, G))
            by rewrite /find_cont/extend !eq_refl.
          by move=>/(dom DOM)=>[G']; exists l, Ty.
        - (*move: E MRG=>/eqP-E /eqP-MRG; move: (prjall_merge E MRG)=> ALL_EQ.
          move=> l Ty G CCl; move: (dom' DOM CCl)=>[iG iFND].
          move: (find_member iFND)=>MEM; move: (GU _ _ _ _ iFND CCl)=>[GU'|//].
          move: (ALL_EQ _ MEM) (cG _ MEM)=>PK cK.
          move: PARTS; rewrite !in_cons F_ne_r T_ne_r /= => PARTS.
          move: PARTS=> /flatten_mapP-[K] /memberP-K_CONT r_in_K.
          move: ((project_parts_in (cG _ K_CONT) (ALL_EQ _ K_CONT)).2 r_in_K).
          rewrite (project_depth cK PK)=>[][m] H.
          by apply/(partof_all_unroll cK GU' PK)/H.*)  admit.
        - move:DOM=>/same_dom_sym-DOM; apply/(same_dom_trans DOM).
          (*by apply/(same_dom_trans _ DL)/(prjall_dom E).*)
          apply (@same_dom_trans _ _ _ _ (find_cont KsL)); [admit|admit].
        - (*move=> l Ty G cL CCl CCLl; right.
          move: (dom' DOM CCl)=>[iG iFND]; move: (find_member iFND)=>MEM.
          move: (cG _ MEM) (gG _ MEM) (NE _ MEM)=>/= {}cG {}gG {}NE.
          move: E MRG=>/eqP-E /eqP-MRG; move: (prjall_merge E MRG).
          move=>/(_ _ MEM)=>/=PRJ.
          move: (GU _ _ _ _ iFND CCl)=>[{}GU|//].
          apply: (CIH _ _ _ _ cG gG NE PRJ GU).
          apply/(LUnroll_EqL LU).
          by move: (cMRG _ _ _ CCLl)=>/EqL_sym.*)
          move=> l Ty cG0 cL0 CCl CCLl; right.
          move: (dom' DOM CCl)=>[iG iFND]; move: (find_member iFND)=>MEM.
          move: (cG _ MEM) (gG _ MEM) (NE _ MEM)=>/= {}cG {}gG {}NE.
          move: (prj_all_find_strong E iFND) =>[iL [memiL [/eqP-iPRJ KsLl]]].
          move: (GU _ _ _ _ iFND CCl)=> [{}GU|//].
          move: (find_cont_map (fun k=> (k.1, l_expand k.2) ) KsLl); rewrite CCLl //= =>[[]]->.
          apply: (CIH _ _ _ _ cG gG NE iPRJ GU); apply: l_expand_unr.
          + by apply: (project_guarded iPRJ).
          + by apply: (proj_lclosed cG iPRJ).
          + by apply: (proj_lne NE iPRJ).
        - apply: merge_correct; [move=> lK memlK|by apply LU|by apply MRG].
          move: E=>/eqP-E; move: (prjall_some2 E memlK)=>[gK [memgK /eqP-prjK]].
          apply/andP; split; [apply /andP| by apply: (proj_lne (NE _ memgK) prjK)].
          by split; [apply (proj_lclosed (cG _ memgK) prjK)| apply (project_guarded prjK)].
Admitted.

Theorem ic_proj r :
  forall iG iL cG cL,
    g_closed iG ->
    guarded 0 iG ->
    non_empty_cont iG ->
    project simple_merge iG r == Some iL ->
    GUnroll iG cG ->
    LUnroll iL cL ->
    Project simple_co_merge r cG cL.
Proof.
  move=> iG iL cG cL CG GG NE Prj GU LU.
  move: (conj CG (conj GG (conj NE (conj Prj (conj GU LU)))))
  => {CG GG Prj GU LU NE}.
  move => /(ex_intro (fun iL=> _) iL) {iL}.
  move => /(ex_intro (fun iG=> _) iG) {iG}.
  move: cG cL; apply/paco2_acc=> r0 _ CIH.

  move: CIH =>/(_ _ _
                  (ex_intro _ _
                     (ex_intro _ _
                        (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))-CIH.
  move=> cG cL [iG] [cG'] [ciG] [giG] [NE] [iGiL] [GU LU].

  move: iGiL  => /eqP-iGiL.
  move: (project_unroll (rec_depth iG) ciG iGiL) => [U1] [U2] [L] [proj] U12.
  move: LU =>/(LUnroll_ind U1); move: U12=>->; rewrite -LUnroll_ind=>UL.
  move : GU (unroll_guarded ciG giG)=>/(GUnroll_ind (rec_depth iG))=>GU nrG.
  move: (g_guarded_nunroll (rec_depth iG) ciG giG)=>guiG.
  move: (g_closed_unroll (rec_depth iG) ciG)=>cuiG {ciG giG iGiL}.
  move: (ne_unr (rec_depth iG) NE)=>{}NE.
  by apply/(project_nonrec CIH cuiG guiG NE nrG proj).
Qed.

Theorem coind_proj r G L :
  g_precond G ->
  project simple_merge G r == Some L ->
  Project simple_co_merge r (g_expand G) (l_expand L).
Proof.
  rewrite/g_precond=>/andP-[/andP-[cG gG] NE] P.
  move: (proj_lclosed cG P) (project_guarded P) (proj_lne NE P)=>cL gL NEl.
  move: (g_expand_unr gG cG NE) (l_expand_unr gL cL NEl)=>{cL gL NEl}.
  by apply/ic_proj.
Qed.

Theorem expand_eProject (g : g_ty) (e : seq (role * l_ty))
  : eproject simple_merge g = Some e ->
    eProject simple_co_merge (ig_end (g_expand g)) (expand_env e).
Proof.
  move=>EPRJ p; constructor.
  have PRE: g_precond g by move: EPRJ;rewrite/eproject;case:ifP.
  move: (precond_parts PRE); case: (boolP (nilp (participants g))).
  + move=> NOPARTS [//|END]; move: EPRJ; rewrite /eproject PRE.
    move: (participants g) NOPARTS=>[]//= _ [<-].
    rewrite /look -in_expanded_env/= (expand_g_end END).
    apply/paco2_fold/prj_end; first by case E: _ / =>//.
      by apply/paco1_fold; constructor.
  + move=>NE _.
    have cG: g_closed g by move: PRE=>/andP-[/andP-[cG gG] CNE].
    have gG: guarded 0 g by move: PRE=>/andP-[/andP-[_ gG] CNE].
    have CNE: non_empty_cont g by move: PRE=>/andP-[_ CNE].
    have GU: GUnroll g (g_expand g) by apply/(g_expand_unr gG cG CNE).
    move: (eproject_some EPRJ NE)=>[q [L] /eqP-PRJ'].
    have gWF: WF (g_expand g) by apply/(project_wf cG gG CNE PRJ' GU).
    move=>{PRJ' L q}.
    case: (boolP (p \in participants g)).
  - move=>PS; move: EPRJ=>/eqP/eproject_part/(_ _ PS)-PRJ.
    rewrite /look -in_expanded_env.
    have ->: (odflt rl_end (omap l_expand (find_cont e p)))
    = l_expand (odflt l_end (find_cont e p))
      by case: find_cont=>//=;rewrite (rltyU (l_expand _)).
      by apply/coind_proj=>//; apply/eqP.
  - move=>PARTS; have NP: ~ part_of p (g_expand g)
            by move=> P_of; move: PARTS; rewrite (partof_unroll cG gG GU).
    rewrite /look -in_expanded_env (fnd_not_part EPRJ PARTS)/=.
      by apply/paco2_fold/prj_end.
Qed.

End Correctness.
