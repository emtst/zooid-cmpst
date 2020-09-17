From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco1 paco2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.
Require Import MPST.Local.
Require Import MPST.Session.

Require Import MPST.Projection.IProject.
Require Import MPST.Projection.PartialProj.

Notation project := (project simple_merge).
Notation prj_all := (prj_all simple_merge).

Definition full_project G p q :=
  match project G p with
  | Some L => partial_proj L q
  | None => None
  end.

Definition fullproj_all Ks p q :=
  match prj_all Ks p with
  | Some LKs => pprj_all LKs q
  | None => None
  end.

Lemma fullproject_some p q G L S
  : project G p == Some L -> partial_proj L q == Some S ->
    full_project G p q = Some S.
Proof. by rewrite /full_project =>/eqP-> /eqP. Qed.

Lemma def_fprojall p q G L S
  : prj_all G p == Some L -> pprj_all L q == Some S ->
    fullproj_all G p q = Some S.
Proof. by rewrite /fullproj_all =>/eqP-> /eqP. Qed.

Lemma dualproj_msg Ks p q Ks0 Ks1 S S' a1 a2 :
  (forall (s s0 : seq (lbl * (mty * s_ty))),
      fullproj_all Ks p q == Some s ->
      fullproj_all Ks q p == Some s0 ->
      s0 = [seq (x.1, (x.2.1, dual x.2.2)) | x <- s]) ->
  a2 == dual_act a1 ->
  prj_all Ks p = Some Ks0 ->
  prj_all Ks q = Some Ks1 ->
  partial_proj (l_msg a1 q Ks0) q == Some S ->
  partial_proj (l_msg a2 p Ks1) p == Some S' ->
  S' = dual S.
Proof.
  move=> Ih /eqP-a12 Lp Lq; rewrite !partialproj_all !eq_refl.
  case Kspq: pprj_all => [Ks0'|//].
  case Ksqp: pprj_all => [Ks1'|//].
  move=> /eqP-[<-]/eqP-[<-]/=; congr s_msg=>//.
  by rewrite (Ih Ks0' Ks1') /fullproj_all ?Lp ?Kspq ?Lq ?Ksqp.
Qed.

Lemma dualproj_all Ks p q Ks0 Ks1 S S' s a :
  (forall s s0 : seq (lbl * (mty * s_ty)),
      fullproj_all Ks p q == Some s ->
      fullproj_all Ks q p == Some s0 ->
      s0 = [seq (x.1, (x.2.1, dual x.2.2)) | x <- s]) ->
  prj_all Ks p = Some Ks0 ->
  prj_all Ks q = Some Ks1 ->
  (s == q) = false ->
  partial_proj (l_msg a s Ks0) q == Some S ->
  match lmerge_all [seq K.2.2 | K <- Ks1] with
  | Some L => partial_proj L p
  | None => None
  end == Some S' ->
  S' = dual S.
Proof.
  move=> Ih Ksp Ksq s_neq_q; rewrite !partialproj_all s_neq_q.
  case Kspq: pprj_all => [Ks0'|//]; move => EqS.
  case Ksqp: lmerge_all => [L'|//].
  move: Ksqp=>/eqP-Ksqp  L'S'.
  move: (mergeall_pprj Ksqp L'S')=>[Ks' [/eqP-Ks1p /eqP-H]]; move: H EqS.
  rewrite (Ih Ks0' Ks' ) /fullproj_all ?Ksp ?Kspq ?Ksq//.
  rewrite -map_comp /comp/= -{1}(dualK S').
  by move=>/(fun_mergeall dualI)/eqP-> /eqP-[<-]; rewrite dualK.
Qed.

Lemma dualproj_all2 Ks p q Ks0 Ks1 S S' s a :
  (forall s s0 : seq (lbl * (mty * s_ty)),
      fullproj_all Ks p q == Some s ->
      fullproj_all Ks q p == Some s0 ->
      s0 = [seq (x.1, (x.2.1, dual x.2.2)) | x <- s]) ->
  prj_all Ks p = Some Ks0 ->
  prj_all Ks q = Some Ks1 ->
  (s == p) = false ->
  match lmerge_all [seq K.2.2 | K <- Ks0] with
  | Some L => partial_proj L q
  | None => None
  end == Some S ->
  partial_proj (l_msg a s Ks1) p == Some S' ->
  S' = dual S.
Proof.
  move=> Ih Ksp Ksq s_neq_q; rewrite !partialproj_all s_neq_q.
  case Kspq: pprj_all => [Ks0'|//].
  case Ksqp: lmerge_all => [L'|//].
  move: Ksqp=>/eqP-Ksqp  L'S'.
  move: (mergeall_pprj Ksqp L'S')=>[Ks' [/eqP-Ks1p /eqP-H]]; move: H.
  rewrite (Ih Ks' Ks0' ) /fullproj_all ?Ksp ?Ksq ?Kspq//.
  rewrite -map_comp /comp/= -{1}(dualK S').
  move=>H1 /(fun_mergeall dualI)/eqP-H2; move: H2 H1.
  by move=>->/eqP-[<-]; rewrite dualK.
Qed.

Lemma fprojall_eq Ks p q Ks0 Ks1
  : (forall K, member K Ks ->
               forall S S', full_project K.2.2 p q == Some S ->
                            full_project K.2.2 q p == Some S' ->
                            S' = dual S) ->
    fullproj_all Ks p q == Some Ks0 ->
    fullproj_all Ks q p == Some Ks1 ->
    Ks1 = [seq (x.1, (x.2.1, dual x.2.2)) | x <- Ks0].
Proof.
  elim: Ks =>[|K Ks Ih] /= in Ks0 Ks1 *.
  - by move=> H; rewrite /fullproj_all/==>/eqP-[<-]/eqP-[<-].
  - move=> H; rewrite /fullproj_all/=.
    case Kp: project =>[Lp|]//; case Ksp: prj_all =>[Lsp|]//=.
    case Ep: partial_proj =>[Sp|]//; case Esp: pprj_all =>[Ssp|]//=.
    case Kq: project =>[Lq|]//; case Ksq: prj_all=>[Lsq|]//=.
    case Eq: partial_proj=>[Sq|]//; case Esq: pprj_all=>[Ssq|]//=.
    move=>/eqP-[<-]/eqP-[<-]/=.
    rewrite -(H K _ Sp Sq) /full_project ?Kp ?Ep ?Kq ?Eq //; last (by left).
    congr cons; apply/Ih; rewrite /fullproj_all ?Ksp ?Esp ?Ksq ?Esq//.
    by move=> K0 K0Ks; apply/H; right.
Qed.

Lemma pproj_notin_binds n G Lp Lq p q S
      (PRJp : project G p = Some Lp)
      (BLp : l_binds n Lp)
      (PRJq : project G q = Some Lq)
      (PPRJ : partial_proj Lq p = Some S)
  : s_binds n S.
Proof.
  elim: G=>[|v|G Ih|r s Ks Ih] in n S Lp Lq PPRJ BLp PRJp PRJq *.
  - by move: PRJp BLp=> [<-].
  - by move: PRJp BLp PRJq PPRJ=>[<-]/= vn [<-] [<-].
  - move: PRJp PRJq => /=.
    case PRJp: project=>[Lp'|//] [ELp]; move: ELp BLp =><-{Lp}BLp.
    case PRJq: project=>[Lq'|//] [ELq]; move: ELq PPRJ=><-{Lq}.
    move: BLp; case: ifP=>//= BLp.
    case: ifP; first (by move=>/(project_binds_eq PRJq PRJp)-C /C; rewrite BLp).
    move=>/= BLq BLp'; case PPRJ: partial_proj=>[S'|//].
    move: (Ih _ _ _ _ PPRJ BLp' PRJp PRJq) => SB.
    case: ifP=>/=; first by move/(sbinds_eq SB).
    by move=> _ [<-]/=.
  - move: PRJp PRJq; rewrite !project_msg.
    case PRJp: prj_all=>[KSp'|//]; case PRJq: prj_all=>[KSq'|//].
    do 3 case: ifP=>//; try (by move=>_ _ _ [ELp]; move: ELp BLp=><-).
    move=> Esp Erp Ers MRGp.
    do ! case: ifP=>//.
    * move=>/eqP-Erq; move=>[ELq]; move: ELq PPRJ=><-.
      rewrite partialproj_all Esp; case PPRJ: pprj_all=>[KsS|//] MRGq.
      move: (prjall_merge_cons PRJp MRGp) => [K MK].
      move: PRJp PRJq MRGp MRGq PPRJ=>/eqP-PRJp /eqP-PRJq /eqP-MRGp /eqP-MRGq /eqP-PPRJ.
      move: (prjall_merge PRJp MRGp MK)=>H0.
      move: (prjall_some PRJq MK)=> [Lq' /=[MKq' PRJq']].
      move: (pprjall_merge PPRJ MRGq MKq')=>/=H1.
      by move: H1 H0 PRJq'=>/eqP-H1 /eqP; apply/Ih.
    * move=>/eqP-Esq Erq; move=>[ELq]; move: ELq PPRJ=><-.
      rewrite partialproj_all Erp; case PPRJ: pprj_all=>[KsS|//] MRGq.
      move: (prjall_merge_cons PRJp MRGp) => [K MK].
      move: PRJp PRJq MRGp MRGq PPRJ=>/eqP-PRJp /eqP-PRJq /eqP-MRGp /eqP-MRGq /eqP-PPRJ.
      move: (prjall_merge PRJp MRGp MK)=>H0.
      move: (prjall_some PRJq MK)=> [Lq' /=[MKq' PRJq']].
      move: (pprjall_merge PPRJ MRGq MKq')=>/=H1.
      by move: H1 H0 PRJq'=>/eqP-H1 /eqP; apply/Ih.
    * move=> Esq Erq MRGq.
      move: (prjall_merge_cons PRJp MRGp) => [K MK].
      move: PRJp PRJq MRGp MRGq=>/eqP-PRJp /eqP-PRJq /eqP-MRGp /eqP-MRGq.
      move: (prjall_merge PRJp MRGp MK)=>/eqP-H0.
      move: (prjall_merge PRJq MRGq MK)=>/eqP.
      by apply/Ih=>//; first by apply: BLp.
Qed.

Lemma all_compat G S S' p q :
  p != q ->
  full_project G p q == Some S ->
  full_project G q p == Some S' ->
  S' = dual S.
Proof.
  move=>/negPf-p_neq_q.
  elim: G => [|v|G Ih| r s Ks Ih] in S S' *.
  - by do ! (move=>/eqP-[<-]).
  - by do ! (move=>/eqP-[<-]).
  - rewrite /full_project/=.
    case Ep: project=>[Lp|//]; case Eq: project=>[Lq|//].
    case: ifP; case: ifP=>//=.
    * by move=> _ _ /eqP-[<-] /eqP-[<-].
    * case Eqp: partial_proj=>[Sq|//] _ Bp.
      by rewrite (pproj_notin_binds Ep Bp Eq Eqp)=>/eqP-[<-] /eqP-[<-].
    * case Eqp: partial_proj=>[Sq|//] Bq _.
      by rewrite (pproj_notin_binds Eq Bq Ep Eqp)=>/eqP-[<-] /eqP-[<-].
    * case Eqp: partial_proj=>[Sq|//]; case Epq: partial_proj=>[Sp|//].
      move: Ep Eq Eqp Epq=>/eqP-Ep /eqP-Eq /eqP-Eqp /eqP-Epq.
      move: (fullproject_some Ep Eqp)=>/eqP-Ppq.
      move: (fullproject_some Eq Epq)=>/eqP-Pqp.
      move: (Ih _ _ Ppq Pqp)=>-> _ _.
      rewrite sbinds_dual; case: ifP; first by move=>_ /eqP-[<-]/eqP-[<-].
      by move=> _ /eqP-[<-] /eqP-[<-].
  - move: Ih=>/fprojall_eq-Ih; rewrite /full_project !project_msg.
    case Ksp: prj_all => [Ks0|//]; case Ksq: prj_all => [Ks1|//].
    case: ifP=>// -r_neq_s.
    do ! (case: ifP=>[/eqP->|]//; rewrite ?p_neq_q ?r_neq_s //).
    * by apply: (dualproj_msg Ih).
    * by apply: (dualproj_all Ih).
    * by move=> _; apply: (dualproj_msg Ih).
    * by move=> r_neq_q _; apply: (dualproj_all Ih).
    * by move=> s_neq_p _; apply: (dualproj_all2 Ih).
    * by move=> _ _ r_neq_p; apply: (dualproj_all2 Ih).
    * case M_Ks0: (lmerge_all [seq K.2.2 | K <- Ks0]) => [L'|//].
      case M_Ks1: (lmerge_all [seq K.2.2 | K <- Ks1]) => [L|//].
      move: M_Ks0 M_Ks1 =>/eqP-M_Ks0 /eqP-M_Ks1 _ _ _ _ L'S LS'.
      move: (mergeall_pprj M_Ks0 L'S)=>[Ks' [/eqP-Ks0q /eqP-H]]; move: H.
      move: (mergeall_pprj M_Ks1 LS')=>[Ks'' [/eqP-Ks1p /eqP-H]]; move: H.
      rewrite (Ih Ks' Ks'') /fullproj_all ?Ksp ?Ksq // -map_comp/comp/=.
      rewrite -{1}(dualK S'); move=>/(fun_mergeall dualI)/eqP->/eqP-[<-].
      by rewrite dualK.
Qed.
