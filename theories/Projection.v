From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.AtomSets.
Require Import MPST.Forall.
Require Import MPST.LNVar.
Require Import MPST.Global.
Require Import MPST.Local.
Require Import MPST.Session.
Require Import MPST.Actions.

Section IProject.

  Open Scope mpst_scope.

  Notation sfv a := (s_var (fv a)).
  Notation sbv n := (s_var (bv _ n)).

  Fixpoint merge (A: eqType) (oL : A) (K : seq A) :=
    match K with
    | [::] => Some oL
    | h::t => if h == oL then merge oL t
              else None
    end.

  Definition merge_all (A : eqType) (K : seq A) :=
    match K with
    | h :: t => merge h t
    | _ => None
    end.

  Fixpoint partial_proj (l : l_ty) (r : role) : option s_ty :=
    match l with
    | l_end => Some (s_end)
    | l_var v => Some (s_var v)
    | l_rec L =>
      match partial_proj L r with
      | Some s => Some (if s == sbv 0 then s_end else s_rec s)
      | _ => None
      end
    | l_msg a p Ks =>
      match (fix prj_all Ks r :=
               match Ks with
               | [::] => Some [::]
               | K::Ks =>
                 match partial_proj K.cnt r, prj_all Ks r with
                 | Some s, Some Ks => Some ((K.lbl, (K.mty, s)) :: Ks)
                 | _, _ => None
                 end
               end
            ) Ks r with
      | Some Ks => if p == r then Some (s_msg a Ks)
                   else merge_all [seq K.cnt | K <- Ks]
      | None => None
      end
    end.

  Fixpoint pprj_all (Ks : seq (lbl * (mty * l_ty))) (r : role)
    : option (seq (lbl * (mty * s_ty))) :=
    match Ks with
    | [::] => Some [::]
    | K::Ks => match partial_proj K.cnt r, pprj_all Ks r with
               | Some s, Some Ks => Some ((K.lbl, (K.mty, s)) :: Ks)
               | _, _ => None
               end
    end.

  Lemma partialproj_all a p Ks r
    : partial_proj (l_msg a p Ks) r =
      match pprj_all Ks r with
      | Some Ks' => if p == r then Some (s_msg a Ks')
                    else merge_all [seq K.cnt | K <- Ks']
      | None => None
      end.
  Proof. by []. Qed.

  Notation Lfv a := (l_var (fv a)).
  Notation lbv n := (l_var (bv _ n)).

  Fixpoint project (g : g_ty) (r : role) : option l_ty :=
    match g with
    | g_end => Some l_end
    | g_var v => Some (l_var v)
    | g_rec G =>
      match project G r with
      | Some L => Some (if L == lbv 0 then l_end else l_rec L)
      | None => None
      end
    | g_msg p q Ks =>
      match (fix proj_all Ks r :=
               match Ks with
               | [::] => Some [::]
               | K::Ks =>
                 match project K.cnt r, proj_all Ks r with
                 | Some L, Some Ks => Some ((K.lbl, (K.mty, L)) :: Ks)
                 | _, _ => None
                 end
               end
            ) Ks r with
      | Some Ks => if p == q then None
                   else if p == r then Some (l_msg l_send q Ks)
                        else if q == r then Some (l_msg l_recv p Ks)
                             else merge_all [seq K.cnt | K <- Ks]
      | None => None
      end
    end.

  Fixpoint prj_all (Ks : seq (lbl * (mty * g_ty))) (r : role)
    : option (seq (lbl * (mty * l_ty))) :=
    match Ks with
    | [::] => Some [::]
    | K::Ks => match project K.cnt r, prj_all Ks r with
               | Some L, Some Ks => Some ((K.lbl, (K.mty, L)) :: Ks)
               | _, _ => None
               end
    end.

  Lemma project_msg p q Ks r
    : project (g_msg p q Ks) r =
      match prj_all Ks r with
      | Some Ks' => if p == q then None
                   else if p == r then Some (l_msg l_send q Ks')
                        else if q == r then Some (l_msg l_recv p Ks')
                             else merge_all [seq K.cnt | K <- Ks']
      | None => None
      end.
  Proof. by []. Qed.

  Lemma prjall_some p Ks Ks' :
    prj_all Ks p == Some Ks' ->
    forall K, member K Ks ->
              exists L, member (K.lbl, (K.mty, L)) Ks' /\
                        project K.cnt p = Some L.
  Proof.
    elim: Ks => [|K Ks Ih]//= in Ks' *.
    case Kp: (project K.cnt p) => [Lp|//].
    case Ksp: (prj_all Ks p) => [LKs|//]; move: Ksp=>/eqP-Ksp.
    move=> /eqP-[Eq]; move: Eq Ih =><- Ih {Ks'} K0 [->{K0}|].
    - by exists Lp; split=>//=; left.
    - by move=> /(Ih LKs Ksp K0)-[L [L_LKs PrjL]]; exists L; split=>//=; right.
  Qed.

  Lemma prjall_some2 p Ks Ks' :
    prj_all Ks p == Some Ks' ->
    forall K, member K Ks' ->
              exists G, member (K.lbl, (K.mty, G)) Ks /\
                        project G p = Some K.cnt.
  Proof.
    elim: Ks' => [|K Ks' Ih]//= in Ks *.
    case: Ks=>// Kg Ks/=.
    case Kgp: (project Kg.cnt p) => [Lp|//].
    case Ksp: (prj_all Ks p) => [Ks''|//]; move: Ksp=>/eqP-Ksp.
    move=>/eqP-[[<-{K} EqKs'']]; move: EqKs'' Ksp=>->Ksp {Ks''}.
    move=> K [->{K}|].
    - by exists (Kg.cnt) =>/=; split=>//; left; case: Kg {Kgp} => l [t G].
    - move=> M; move: (Ih Ks Ksp K M)=>[G [MG prjG]].
      by exists G; split=>//; right.
  Qed.

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
    (forall s s0 : seq (lbl * (mty * s_ty)),
        fullproj_all Ks p q == Some s ->
        fullproj_all Ks q p == Some s0 ->
        s0 = [seq (x.lbl, (x.mty, dual x.cnt)) | x <- s]) ->
    a2 == dual_act a1 ->
    prj_all Ks p = Some Ks0 ->
    prj_all Ks q = Some Ks1 ->
    partial_proj (l_msg a1 q Ks0) q == Some S ->
    partial_proj (l_msg a2 p Ks1) p == Some S' ->
    S' = dual S.
  Proof.
    move=> Ih /eqP-a12 Lp Lq; rewrite !partialproj_all !eq_refl.
    case Kspq: (pprj_all Ks0) => [Ks0'|//].
    case Ksqp: (pprj_all Ks1) => [Ks1'|//].
    move=> /eqP-[<-]/eqP-[<-]/=; congr s_msg=>//.
    by rewrite (Ih Ks0' Ks1') /fullproj_all ?Lp ?Kspq ?Lq ?Ksqp.
  Qed.

  Lemma merge_some (A : eqType)
        (K : lbl * (mty * A))
        (Ks : seq (lbl * (mty * A))) L
    : merge K.cnt [seq K0.cnt | K0 <- Ks] == Some L -> K.cnt = L.
  Proof. by elim: Ks=>[/eqP-[]//|K' Ks Ih/=]; case:ifP. Qed.

  Lemma merge_pprj L' Ks L p S
    : merge L' [seq K.cnt | K <- Ks] == Some L -> partial_proj L p == Some S ->
      exists Ks', pprj_all Ks p = Some Ks' /\
                  merge S [seq K.cnt | K <- Ks'] = Some S.
  Proof.
    elim: Ks=>[_|K' Ks Ih]/=; first (by exists [::]; split); move: Ih.
    case: ifP=>///eqP<- Ih M_L'; move: (merge_some M_L')=>-> /eqP-L_S.
    rewrite L_S; move: L_S=>/eqP-L_S; move: (Ih M_L' L_S) => [Ks' [Ksp M_S]].
    by exists ((K'.lbl, (K'.mty, S)):: Ks'); rewrite Ksp /= eq_refl M_S.
  Qed.

  Lemma mergeall_pprj Ks L p S
    : merge_all [seq K.cnt | K <- Ks] == Some L -> partial_proj L p == Some S ->
      exists Ks', pprj_all Ks p = Some Ks' /\
                  merge_all [seq K.cnt | K <- Ks'] = Some S.
  Proof.
    case: Ks=>[//|K Ks]/=; move=> H; move: (merge_some H)=>KL.
    move: KL H=>-> H /eqP-L_S; rewrite L_S; move: L_S=>/eqP-L_S.
    move: (merge_pprj H L_S)=>[Ks' [Ksp M_S]].
    by exists ((K.lbl, (K.mty, S)) :: Ks'); rewrite Ksp/= M_S.
  Qed.

  Lemma fun_mergeall (A B : eqType) (f : A -> B) (Ks : seq (lbl * (mty * A))) X
    : injective f ->
      merge_all [seq f x.cnt | x <- Ks] == Some (f X) ->
      merge_all [seq x.cnt | x <- Ks] == Some X.
  Proof.
    case: Ks=>[//|K Ks/=] I; elim: Ks=>[|K' Ks]//=.
    - by move=>/eqP-[/I->].
    - by move=> Ih; case: ifP=>///eqP-[/I->]; rewrite eq_refl=>/Ih.
  Qed.

  Lemma dualproj_all Ks p q Ks0 Ks1 S S' s a :
    (forall s s0 : seq (lbl * (mty * s_ty)),
        fullproj_all Ks p q == Some s ->
        fullproj_all Ks q p == Some s0 ->
        s0 = [seq (x.lbl, (x.mty, dual x.cnt)) | x <- s]) ->
    prj_all Ks p = Some Ks0 ->
    prj_all Ks q = Some Ks1 ->
    (s == q) = false ->
    partial_proj (l_msg a s Ks0) q == Some S ->
    match merge_all [seq K.cnt | K <- Ks1] with
    | Some L => partial_proj L p
    | None => None
    end == Some S' ->
    S' = dual S.
  Proof.
    move=> Ih Ksp Ksq s_neq_q; rewrite !partialproj_all s_neq_q.
    case Kspq: (pprj_all Ks0) => [Ks0'|//]; move => EqS.
    case Ksqp: (merge_all [seq K.cnt | K <- Ks1]) => [L'|//].
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
        s0 = [seq (x.lbl, (x.mty, dual x.cnt)) | x <- s]) ->
    prj_all Ks p = Some Ks0 ->
    prj_all Ks q = Some Ks1 ->
    (s == p) = false ->
    match merge_all [seq K.cnt | K <- Ks0] with
    | Some L => partial_proj L q
    | None => None
    end == Some S ->
    partial_proj (l_msg a s Ks1) p == Some S' ->
    S' = dual S.
  Proof.
    move=> Ih Ksp Ksq s_neq_q; rewrite !partialproj_all s_neq_q.
    case Kspq: (pprj_all Ks1) => [Ks0'|//].
    case Ksqp: (merge_all [seq K.cnt | K <- Ks0]) => [L'|//].
    move: Ksqp=>/eqP-Ksqp  L'S'.
    move: (mergeall_pprj Ksqp L'S')=>[Ks' [/eqP-Ks1p /eqP-H]]; move: H.
    rewrite (Ih Ks' Ks0' ) /fullproj_all ?Ksp ?Ksq ?Kspq//.
    rewrite -map_comp /comp/= -{1}(dualK S').
    move=>H1 /(fun_mergeall dualI)/eqP-H2; move: H2 H1.
    by move=>->/eqP-[<-]; rewrite dualK.
  Qed.

  Lemma fprojall_eq Ks p q Ks0 Ks1
    : (forall K, member K Ks ->
                 forall S S', full_project K.cnt p q == Some S ->
                              full_project K.cnt q p == Some S' ->
                              S' = dual S) ->
      fullproj_all Ks p q == Some Ks0 ->
      fullproj_all Ks q p == Some Ks1 ->
      Ks1 = [seq (x.lbl, (x.mty, dual x.cnt)) | x <- Ks0].
  Proof.
    elim: Ks =>[|K Ks Ih] /= in Ks0 Ks1 *.
    - by move=> H; rewrite /fullproj_all/==>/eqP-[<-]/eqP-[<-].
    - move=> H; rewrite /fullproj_all/=.
      case Kp: (project K.cnt p)=>[Lp|]//; case Ksp: (prj_all Ks p)=>[Lsp|]//=.
      case Ep: (partial_proj Lp q)=>[Sp|]//; case Esp: (pprj_all Lsp q)=>[Ssp|]//=.
      case Kq: (project K.cnt q)=>[Lq|]//; case Ksq: (prj_all Ks q)=>[Lsq|]//=.
      case Eq: (partial_proj Lq p)=>[Sq|]//; case Esq: (pprj_all Lsq p)=>[Ssq|]//=.
      move=>/eqP-[<-]/eqP-[<-]/=.
      rewrite -(H K _ Sp Sq) /full_project ?Kp ?Ep ?Kq ?Eq //; last (by left).
      congr cons; apply/Ih; rewrite /fullproj_all ?Ksp ?Esp ?Ksq ?Esq//.
      by move=> K0 K0Ks; apply/H; right.
  Qed.

  Lemma prjall_merge p Ks KsL L :
    prj_all Ks p == Some KsL ->
    merge_all [seq K0.cnt | K0 <- KsL] == Some L ->
    forall K, member K Ks -> project K.cnt p == Some L.
  Proof.
    case: KsL=>//= Kl KsL; case: Ks=>//= Kg Ks.
    case Kg_p: project => [Lp | //]; case Ks_p: prj_all => [Ksp | //]/=.
    move=> Eq; move: Eq Ks_p => /eqP-[<-->] /eqP-Prj Mrg {Kl Ksp}.
    move:Mrg (merge_some Mrg)=>/=Mrg Eq; move: Eq Mrg Kg_p=>->Mrg /eqP-Kg_p.
    move=> K [->//|]; move: Prj Mrg K {Lp Kg_p Kg}.
    elim: Ks KsL=>//= Kg Ks Ih KsL.
    case Kg_p: project => [Lp | //]; case Ks_p: prj_all => [Ksp | //]/=.
    move=> Eq; move: Eq Ih Ks_p Kg_p=>/eqP-[<-]//= Ih /eqP-Prj.
    case: ifP=>[/eqP-> {Lp}|//] /eqP-Kg_p Mrg K [->//|].
    by move: Prj=>/Ih/(_ Mrg K).
  Qed.

  Lemma project_var_notin p G v L :
    (L == l_end) || (L == l_var v) ->
    project G p == Some L ->
    p \notin participants G.
  Proof.
    elim/gty_ind1: G => [|v'|G Ih|q r Ks Ih]// in L v *.
    - move: Ih=>/=; case: (project G p)=>[Lp|//] Ih.
      move=>/orP-[/eqP->|/eqP->]; case: ifP=>[/eqP-Lp_var|]//.
      move: Lp_var Ih =>-> /(_ (lbv 0) (bv _ 0))-Ih _.
      by apply:Ih; rewrite eq_refl // orbC.
    - rewrite project_msg; case E: (prj_all _ _)=>[KsL|//]; move: E=>/eqP-E/=.
      case: ifP=>[//|/(rwP negPf)-q_ne_r].
      case: ifP=>[/eqP->/orP-[/eqP->|/eqP->]//|/(rwP negPf)-q_ne_p].
      case: ifP=>[/eqP->/orP-[/eqP->|/eqP->]//|/(rwP negPf)-r_ne_p].
      do 2 rewrite in_cons negb_or; move=> L_end_var M_some.
      do 2 rewrite eq_sym ?q_ne_p /= ?r_ne_p /=; move: M_some.
      move: E=>/prjall_merge-E /E-Prjall.
      apply/flatten_mapP=>[[Kg /memberP-M]].
      by apply/negP; apply: (Ih _ M L v L_end_var); apply: Prjall.
  Qed.

  Lemma projectmsg_var p r s Ks :
    project (g_msg r s Ks) p == Some (lbv 0) ->
    r != p /\ s != p /\ r != s /\
    (forall K, member K Ks -> project K.cnt p == Some (lbv 0)).
  Proof.
    rewrite project_msg; case Ksp: prj_all => [Ks'|//]; move: Ksp=>/eqP.
    do ! case: ifP=>//; move=>s_ne_p r_ne_p r_ne_s.
    by move=>/prjall_merge-H /H.
  Qed.

  Lemma pprjall_merge p Ks KsL L :
    pprj_all Ks p == Some KsL ->
    merge_all [seq K0.cnt | K0 <- KsL] == Some L ->
    forall K, member K Ks -> partial_proj K.cnt p == Some L.
  Proof.
    case: KsL=>//= Kl KsL; case: Ks=>//= Kg Ks.
    case Kg_p: partial_proj => [Lp | //]; case Ks_p: pprj_all => [Ksp | //]/=.
    move=> Eq; move: Eq Ks_p => /eqP-[<-->] /eqP-Prj Mrg {Kl Ksp}.
    move:Mrg (merge_some Mrg)=>/=Mrg Eq; move: Eq Mrg Kg_p=>->Mrg /eqP-Kg_p.
    move=> K [->//|]; move: Prj Mrg K {Lp Kg_p Kg}.
    elim: Ks KsL=>//= Kg Ks Ih KsL.
    case Kg_p: partial_proj => [Lp | //]; case Ks_p: pprj_all => [Ksp | //]/=.
    move=> Eq; move: Eq Ih Ks_p Kg_p=>/eqP-[<-]//= Ih /eqP-Prj.
    case: ifP=>[/eqP-> {Lp}|//] /eqP-Kg_p Mrg K [->//|].
    by move: Prj=>/Ih/(_ Mrg K).
  Qed.

  Lemma pprjall_some p Ks Ks' :
    pprj_all Ks p == Some Ks' ->
    forall K,
      member K Ks ->
      exists L, member (K.lbl, (K.mty, L)) Ks' /\ partial_proj K.cnt p = Some L.
  Admitted.

  Lemma pproj_var p q G Lq Sq :
    project G p == Some (lbv 0) ->
    project G q == Some Lq ->
    partial_proj Lq p == Some Sq ->
    Sq = sbv 0.
  Proof.
    elim/gty_ind1: G =>[//|v//=|G Ih//=|r s Ks Ih] in Lq Sq *.
    - by move=>/eqP-[->]/eqP-[<-]/=/eqP-[<-].
    - by case: project=>//L; case: ifP.
    - move=> /projectmsg_var-[r_ne_p [s_ne_p [r_ne_s Ksp]]].
      rewrite project_msg; case Eq: prj_all=>[KsL|//]; move: Eq=>/eqP-Prj_Ks.
      rewrite (negPf r_ne_s); do ! case: ifP=>[_ /eqP-[<-]|_].
      * rewrite partialproj_all (negPf s_ne_p); case E: pprj_all=>[KsS|//] Mrg.
        have [K KKs]: exists K, member K Ks
            by move=>{Ih Ksp}; case: Ks Prj_Ks E Mrg;
                       first (by move=>/eqP-[<-] [<-]);
                       move=> K; exists K; left.
        move: E Mrg Prj_Ks =>/eqP-E /(pprjall_merge E)-Mrg /prjall_some-Prj_Ks.
        move:Prj_Ks Ksp =>/(_ K KKs)-[L [ML /eqP-KL]] /(_ K KKs)-Kp.
        by move: Mrg Ih => /(_ _ ML)-Pprj /(_ _ KKs L Sq Kp KL Pprj).
      * rewrite partialproj_all (negPf r_ne_p); case E: pprj_all=>[KsS|//] Mrg.
        have [K KKs]: exists K, member K Ks
            by move=>{Ih Ksp}; case: Ks Prj_Ks E Mrg;
                       first (by move=>/eqP-[<-] [<-]);
                       move=> K; exists K; left.
        move: E Mrg Prj_Ks =>/eqP-E /(pprjall_merge E)-Mrg /prjall_some-Prj_Ks.
        move:Prj_Ks Ksp =>/(_ K KKs)-[L [ML /eqP-KL]] /(_ K KKs)-Kp.
        by move: Mrg Ih => /(_ _ ML)-Pprj /(_ _ KKs L Sq Kp KL Pprj).
      * move=> Mrg PPrj.
        suff : exists K, member K Ks by
              move=>[K M]; move: Mrg=>/(prjall_merge Prj_Ks)-Ksq{Prj_Ks};
                      move: Ih=>/(_ K M _ _ (Ksp _ M) (Ksq _ M) PPrj)-Ih.
        case: Ks Prj_Ks {Ih Ksp}=>[//=|K Ks _]; last (by exists K; left).
        by move=>/eqP-[Eq]; move: Eq Mrg=><-.
  Qed.

  Lemma all_compat G S S' p q :
    p != q ->
    full_project G p q == Some S ->
    full_project G q p == Some S' ->
    S' = dual S.
  Proof.
    move=>/negPf-p_neq_q.
    elim/gty_ind1: G => [|v|G Ih| r s Ks Ih] in S S' *.
    - by do ! (move=>/eqP-[<-]).
    - by do ! (move=>/eqP-[<-]).
    - rewrite /full_project/=.
      case Ep: project=>[Lp|//]; case Eq: project=>[Lq|//].
      move: Ep Eq; do ! case: ifP=>[/eqP->//=|//=].
      * by move=> _ _ /eqP-[<-] /eqP-[<-].
      * case Eq: partial_proj=>[Sq|]//; move: Eq=>/eqP-Eq.
        move=>_ /eqP-Gp_var /eqP-Gq_Lq; move: (pproj_var Gp_var Gq_Lq Eq)=>->.
        by rewrite eq_refl=>/eqP-[<-] /eqP-[<-].
      * case Eq: partial_proj=>[Sq|]//; move: Eq=>/eqP-Eq.
        move=>_ /eqP-Gp /eqP-Gq; move: (pproj_var Gq Gp Eq)=>->.
        by rewrite eq_refl=>/eqP-[<-] /eqP-[<-].
      * case Ep: partial_proj=>[Sp|]//; move: Ep=>/eqP-Ep.
        case Eq: partial_proj=>[Sq|]//; move: Eq=>/eqP-Eq.
        move=>_ _ /eqP-Prj_p /eqP-Prj_q.
        move: Prj_p Ep =>/fullproject_some-Prj_p /Prj_p/eqP/Ih-{Prj_p Ih}Ih.
        move: Prj_q Eq =>/fullproject_some-Prj_q /Prj_q/eqP/Ih-{Prj_q Ih}Ih.
        move: Ih; case: ifP=>[/eqP->->//= /eqP-[<-] /eqP-[<-]//|H -> /eqP-[<-]].
        by move: H; rewrite -{1}(dualK Sp); case: ifP=>[/eqP->//|_ _ /eqP-[<-]].
    - move: Ih=>/fprojall_eq-Ih; rewrite /full_project !project_msg.
      case Ksp: (prj_all Ks) => [Ks0|//]; case Ksq: (prj_all Ks) => [Ks1|//].
      case: ifP=>// -r_neq_s.
      do ! (case: ifP=>[/eqP->|]//; rewrite ?p_neq_q ?r_neq_s //).
      * by apply: (dualproj_msg Ih).
      * by apply: (dualproj_all Ih).
      * by move=> _; apply: (dualproj_msg Ih).
      * by move=> r_neq_q _; apply: (dualproj_all Ih).
      * by move=> s_neq_p _; apply: (dualproj_all2 Ih).
      * by move=> _ _ r_neq_p; apply: (dualproj_all2 Ih).
      * case M_Ks0: (merge_all [seq K.cnt | K <- Ks0]) => [L'|//].
        case M_Ks1: (merge_all [seq K.cnt | K <- Ks1]) => [L|//].
        move: M_Ks0 M_Ks1 =>/eqP-M_Ks0 /eqP-M_Ks1 _ _ _ _ L'S LS'.
        move: (mergeall_pprj M_Ks0 L'S)=>[Ks' [/eqP-Ks0q /eqP-H]]; move: H.
        move: (mergeall_pprj M_Ks1 LS')=>[Ks'' [/eqP-Ks1p /eqP-H]]; move: H.
        rewrite (Ih Ks' Ks'') /fullproj_all ?Ksp ?Ksq // -map_comp/comp/=.
        rewrite -{1}(dualK S'); move=>/(fun_mergeall dualI)/eqP->/eqP-[<-].
        by rewrite dualK.
  Qed.
End IProject.

Section CProject.

  CoInductive EqL : rl_ty -> rl_ty -> Prop :=
  | el_end : EqL rl_end rl_end
  | el_msg a p Ks1 Ks2 :
      AllEqL Ks1 Ks2 ->
      EqL (rl_msg a p Ks1) (rl_msg a p Ks2)
  with AllEqL : seq (lbl * (mty * rl_ty)) ->
                seq (lbl * (mty * rl_ty)) ->
                Prop :=
  | el_nil : AllEqL [::] [::]
  | el_cons l t L1 L2 Ks1 Ks2 :
      EqL L1 L2 ->
      AllEqL Ks1 Ks2 ->
      AllEqL ((l, (t, L1)) :: Ks1) ((l, (t, L2)) :: Ks2).

  Inductive Merge : seq (lbl * (mty * rl_ty)) -> rl_ty -> Prop :=
  | m_nil l t L : Merge [:: (l, (t, L))] L
  | m_cons l t L1 L2 Ks :
      EqL L1 L2 ->
      Merge Ks L2 ->
      Merge ((l, (t, L1)) :: Ks) L2.

  CoInductive Project (p : role) : rg_ty -> rl_ty -> Prop :=
  | prj_end : Project p rg_end rl_end
  | prj_send1 q KsG KsL :
      p != q ->
      ProjectAll p KsG KsL ->
      Project p (rg_msg None p q KsG) (rl_msg l_send q KsL)
  | prj_send2 l t q KsG KsL L :
      p != q ->
      ProjectAll p KsG KsL ->
      lookup l KsL = Some (t, L) ->
      Project p (rg_msg (Some l) p q KsG) L
  | prj_recv o q KsG KsL :
      p != q ->
      ProjectAll p KsG KsL ->
      Project p (rg_msg o q p KsG) (rl_msg l_recv q KsL)
  | prj_mrg o q r KsG KsL L :
      q != r ->
      p != q ->
      p != r ->
      ProjectAll p KsG KsL ->
      Merge KsL L ->
      Project p (rg_msg o q r KsG) L
  with ProjectAll (p : role) :
         seq (lbl * (mty * rg_ty)) ->
         seq (lbl * (mty * rl_ty)) ->
         Prop :=
  | prj_nil  : ProjectAll p [::] [::]
  | prj_cons l t G L KsG KsL :
      Project p G L ->
      ProjectAll p KsG KsL ->
      ProjectAll p ((l, (t, G)) :: KsG) ((l, (t, L)) :: KsL)
  .

  Lemma project_rec G r L :
    project G r == Some L ->
    ((L == l_var (bv _ 0)) = false) ->
    project (g_rec G) r = Some (l_rec L).
  Proof. by move=>/=/eqP-[->] ->. Qed.

  Lemma gclosed_lclosed G r L :
    g_closed G ->
    project G r == Some L ->
    l_closed L.
  Proof.
    rewrite /g_closed/l_closed; elim/gty_ind1: G L 0 =>[|v|G Ih|p q Ks Ih] L n.
    - by move=> _ /eqP-[<-].
    - case: v=> [a|m /andP-[]]//=; first by rewrite -cardfs_eq0 cardfs1.
      case: ifP; first by rewrite -cardfs_eq0 cardfs1.
      by move=> H _ _ /eqP-[<-]/=; rewrite H.
    - move: Ih=>/=; case Eq: (project G r) =>[Lr|//].
      move=> /(_ Lr n.+1)-Ih; move=>/Ih/(_ (eq_refl _)).
      by case: ifP=>// _ H /eqP-[<-].
    - rewrite project_msg=>/=/andP-[H1 H2].
      case Eq: (prj_all Ks r) => [Ks'|//]; case: ifP=>[//|p_neq_q]/=.
      move: Eq=>/eqP-Eq.
      case: ifP=>[p_eq_r /eqP-[<-]/=|p_neq_r].
      * apply/andP; rewrite !fsetUs_fset0 !member_map in H1 H2 *=> H1 H2.
        apply/all_and2 => K; apply/all_and2=> M; apply/andP.
        move: (prjall_some2 Eq M) =>[G [M' /eqP-PrjG]].
        by apply: (Ih _ M'); first by rewrite H1 // H2.
      * case: ifP=>[q_eq_r /eqP-[<-]|q_neq_r /eqP].
        + apply/andP; rewrite !fsetUs_fset0 !member_map in H1 H2 *=> H1 H2.
          apply/all_and2 => K; apply/all_and2=> M; apply/andP.
          move: (prjall_some2 Eq M) =>[G [M' /eqP-PrjG]].
          by apply: (Ih _ M'); first by rewrite H1 // H2.
        + case: Ks' Eq=>// Kl Ks' Eq /eqP/merge_some<- /=.
          case: Ks Eq Ih H1 H2=>//= Kg Ks.
          case Eqg: (project Kg.2.2 r)=>[Lk|//].
          case EqKs: (prj_all Ks r)=>[Ks''|//].
          rewrite !fsetUs_list=> /eqP-[[<- H2]] Ih /andP-[H3 H4] /andP-[H5 H6].
          by apply: (Ih Kg)=>//=; [left|rewrite H3 H5|apply/eqP].
  Qed.

  Lemma prjall_open r n g l Ks Ks' :
    (forall p : lbl * (mty * g_ty),
      member p Ks ->
      forall s : lty_eqType,
        project p.2.2 r == Some s ->
        project (g_open n g p.2.2) r = Some (l_open n l s)) ->
    prj_all Ks r = Some Ks' ->
    prj_all [seq (K.1, (K.2.1, g_open n g K.2.2)) | K <- Ks] r
    = Some [seq (K.1, (K.2.1, l_open n l K.2.2)) | K <- Ks'].
  Proof.
    elim: Ks Ks' => [|K Ks Ih]; case=>[|K' Ks']//=.
    - by case: (project K.2.2 r); case: (prj_all Ks r).
    - move=> H. move: (H K (or_introl erefl)).
      case: (project K.2.2 r) =>// L /(_ L (eq_refl _))->.
      move: H=>/(_ _ (or_intror _))-H; move: Ih => /(_ _ H) {H}.
      by case: (prj_all Ks r)=>[Ksr|//] /(_ Ksr erefl)-> [<-<-]/=.
  Qed.

  Lemma project_closed G r L :
    project G r == Some L ->
    g_closed (g_rec G) ->
    ((L == l_var (bv _ 0)) = false) ->
    project (g_open 0 (g_rec G) G) r = Some (l_open 0 (l_rec L) L).
  Proof.
    move=> H C L0; move: (project_rec H L0) => Hr; move: 0 {L0} (g_rec G) C (l_rec L) Hr.
    elim/gty_ind1: G L H =>[|v|G Ih|p q Ks Ih] L.
    - by move=>/eqP-[<-].
    - move=> H; move: H =>/eqP-[<-] /= n G' C L'.
      by case: v G' C=>//= m; case: ifP.
    - move:Ih=>/=;case Eq:(project G r)=>[Lr|//].
      move: Eq=> /eqP-Eq /(_ Lr (eq_refl _))-Ih.
      case:ifP=>//H/eqP-[<-] n g cg l prj.
      move: Ih=>/(_ n.+1 g cg l prj)->/=; move: prj=>/eqP-prj.
      case: ifP=>//; move: (gclosed_lclosed cg prj) => cl.
      case: Lr {Eq} H=>//=; case=>//= m; case: ifP; last by move=> _ ->.
      move=> _ _ H; case: l cl {prj} H=>// v.
      (*
      rewrite /l_closed/=; case: v=>//= s /andP-[].
      by rewrite -cardfs_eq0 cardfs1.
       *)
      admit.
      admit.
      admit.
      admit.
      admit.
    - rewrite project_msg.
      case Ksr: (prj_all Ks r) =>[Ks'|//].
      case: ifP=>[//|p_neq_q].
      case: ifP=>[/eqP-p_eq_r|p_neq_r].
      * move=>/eqP-[<-]{L} n g cg l prj_g_l.
        rewrite /g_open -/g_open  /l_open -/l_open.
        rewrite project_msg p_neq_q p_eq_r eq_refl.
        move: Ih => /(_ _ _ _ _ n g cg l prj_g_l)-Ih.
        by move: (prjall_open Ih Ksr)=>->.
      * case: ifP=>[/eqP-q_eq_r|q_neq_r].
        + move=>/eqP-[<-]{L} n g cg l prj_g_l.
          rewrite /g_open -/g_open  /l_open -/l_open.
          rewrite project_msg p_neq_q p_neq_r q_eq_r eq_refl.
          move: Ih => /(_ _ _ _ _ n g cg l prj_g_l)-Ih.
          by move: (prjall_open Ih Ksr)=>->.
        + move=> Mrg n g cg l prj; rewrite /g_open-/g_open project_msg.
          rewrite p_neq_q p_neq_r q_neq_r.
          move: Ih=>/(_ _ _ _ _ n g cg l prj)-Ih.
          move: (prjall_open Ih Ksr)=>->; rewrite -map_comp/comp/=.
          move: Mrg=>{Ksr}; case: Ks'=>//=K Ks'.
          elim: Ks'=>//=; first by move=>/eqP-[->].
          by move=> K' Ks' IhKs; case: ifP=>// /eqP->; rewrite eq_refl=>/IhKs.
  Admitted.

  (*
  Fixpoint gunrollings n G :=
    match n with
    | n.+1 =>
      match G with
      | g_rec G => gunrollings n (g_open 0 (g_rec G) G)
      | _ => G
      end
    | 0 => G
    end.

  Definition gunroll G := gunrollings (depth_gty G) G.

  Lemma gunroll_not_rec G G': gunroll G != g_rec G'.
  *)

  Lemma ic_proj r :
    forall iG iL cG cL,
    g_closed iG ->
    project iG r == Some iL ->
    GUnroll iG cG ->
    LUnroll iL cL ->
    Project r cG cL.
  Proof.
    cofix CIh; case=>[|v|G|]/=.
    - case=>// cG cL _ _ GU.
      case Eq: _ _ / GU =>//; move => {Eq} LU.
      case Eq: _ _ / LU =>//; move => {Eq}.
      by constructor.
    - case=>// v' cG cL _ _ GU.
      by case Eq: _ _ / GU.
    - case Gr: (project G r) => [L|//]; move: Gr=>/eqP-Gr.
      move=> iL cG cL clG; case: ifP=>[//|L_not_var /eqP-[<-] GU LU].
      move=>Eq; move: Eq Gr=>/eqP-> Gr /eqP-[<-]{L iL}.
      case EqG: _ _ /GU=>[//|G'' {cG}cG GU|//]; move: EqG GU=>[<-] GU {G''}.
      case EqL: _ _ /LU=>[//|L'' {cL}cL LU|//]; move: EqL LU=>[<-] LU {L''}.
      move: Gr => /project_closed /(_ clG L_not_var)/eqP-Gr.
      case: cG GU => [GU|].
      case Eq: rg_end /GU =>[|G'' cG' GU|]//.
      admit.
      case: cL LU => [LU|].
      move: clG => /gopen_closed-clG.
      move: clG Gr LU GU.

      elim/gty_ind1: G L Gr GU L_not_var LU.
      * admit.
      * admit.
      case EqG: _ _ /GU=>[//|G'' {cG}cG GU|//]; move: EqG GU=>[<-] GU {G''}.
      case EqL: _ _ /LU=>[//|L'' {cL}cL LU|//]; move: EqL LU=>[<-] LU {L''}.
      admit.
      apply: CIh.

  (*
  CoFixpoint project2 (g : rg_ty) (r : role) : option rl_ty :=
   *)

End CProject.

(*
  Fixpoint project2 (g : rg_ty) (r : role) : option l_ty :=
    match g with
    | g_end => Some l_end
    | g_var v => Some (l_var v)
    | g_rec G =>
      match project2 G r with
      | Some L => if L == lbv 0 then Some l_end else Some (l_rec L)
      | None => None
      end
    | g_msg a p q Ks =>
      match (fix proj_all Ks p :=
               match Ks with
               | [::] => Some [::]
               | K::Ks =>
                 match project2 K.cnt p, proj_all Ks p with
                 | Some L, Some Ks => Some ((K.lbl, (K.mty, L)) :: Ks)
                 | _, _ => None
                 end
               end
            ) Ks r with
      | Some Ks =>
        if p == q then None
        else if a is Some l
             then if lookup l Ks is Some (_, L)
                  then if q == r then Some (l_msg l_recv p Ks)
                       else Some L
                  else None
             else if p == r then Some (l_msg l_send q Ks)
                  else if q == r then Some (l_msg l_recv p Ks)
                       else merge_all [seq K.cnt | K <- Ks]
      | None => None
      end
    end.

  Fixpoint prj_all2 (Ks : seq (lbl * (mty * rg_ty))) (r : role) :=
    match Ks with
    | [::] => Some [::]
    | K::Ks =>
      match project2 K.cnt r, prj_all2 Ks r with
      | Some L, Some Ks => Some ((K.lbl, (K.mty, L)) :: Ks)
      | _, _ => None
      end
    end.

  Fixpoint queue_contents (g : rg_ty) qs :=
    match g with
    | g_end
    | g_rec _
    | g_var _ => Some qs
    | g_msg a p q Ks =>
      match a with
      | Some l =>
        (fix contQueue Ks :=
           match Ks with
           | [::] => None
           | K::Ks => if K.lbl == l
                      then match queue_contents K.cnt qs with
                           | Some Q => Some (enq Q (p,q) (l, K.mty))
                           | None => None
                           end
                      else contQueue Ks
           end) Ks
      | None => match Ks with
                | [::] => None
                | K::_ => queue_contents K.cnt qs
                end
      end
    end%fmap.

  Definition insert (E : role * l_ty) P :=
    match lookup E.1 P with
    | Some _ => P
    | None => E :: P
    end.

  Fixpoint project_all (g : g_ty) (r : seq role) : option (seq (role * l_ty)) :=
    match r with
    | [::] => Some [::]
    | h :: t => match project g h, project_all g t with
                | Some L, Some E => Some (insert (h, L) E)
                | _, _ => None
                end
    end.

  Definition projection (g : g_ty) : option (seq (role * l_ty)) :=
    project_all g (participants g).

  Lemma mergeall_some (T : eqType) (Ks : seq (lbl * (mty * T))) (A : T)
    : merge_all [seq K.cnt | K <- Ks] == Some A ->
      forall K, member K Ks -> K.cnt = A.
  Proof.
    case: Ks=> [|K Ks]//=; elim: Ks => [|K' Ks Ih] in K *.
    - by move=> /eqP-[<-] K' [->|//].
    - rewrite /=; case: ifP=>// /eqP-KK' H K0 [K0K | [K0K' | Next]].
      + by apply: (Ih K)=>//; left.
      + by apply: (Ih K')=>//; first (by rewrite KK'); left.
      + by apply: (Ih K)=>//; right.
  Qed.

  Lemma option_comm A B C (x : option A) (f : A -> option B) (g : B -> C) z z' :
    match
      match x with
      | Some y => f y
      | None => z
      end
    with
    | Some y => g y
    | None => z'
    end =
    match x with
    | Some y => match f y with
                    | Some y => g y
                    | None => z'
                end
    | None => match z with
              | Some y => g y
              | None => z'
              end
    end.
  Proof. by case: x. Qed.

  Lemma fulproj_some_neq a p q r s Ks L
    : full_project (g_msg a r s Ks) p q = Some L ->
      r != s.
  Proof.
    rewrite /full_project project_msg.
    case Ksp: (prj_all Ks p) =>[Lp|//].
    by case: ifP.
  Qed.

  Lemma mergeall_merge (A : eqType) S (Ks : seq (lbl * (mty * A)))
    : merge_all [seq K.cnt | K <- Ks] == Some S ->
      merge S [seq K.cnt | K <- Ks] == Some S.
  Proof.
    case: Ks=>[| K Ks /= H]//=.
    move: (merge_some H)=>/eqP; case: ifP=>///eqP-K_S.
    by move: K_S H=>->.
  Qed.

  Fixpoint proj_ps (G : rg_ty) (ps : seq role) :=
    match ps with
    | [::] => Some [fmap]
    | p :: ps =>
      match project2 G p, proj_ps G ps with
      | Some L, Some E => Some E.[p <- L]
      | _, _ => None
      end
    end%fmap.

  Definition proj_env G := proj_ps G (participants G).

  Notation renv := {fmap role -> l_ty}.
  Notation qenv := {fmap role * role -> seq (lbl * mty) }.
  Notation ralt := {fmap role -> seq (lbl * (mty * l_ty))}.

  Definition proj_cfg G : option (renv * qenv):=
    match proj_env G, queue_contents G [fmap] with
    | Some E, Some Q => Some (E, Q)
    | _, _ => None
    end%fmap.

  Close Scope mpst_scope.


  Lemma proj_send p q KsG E :
    proj_env (g_msg None p q KsG) == Some E ->
    exists KsL, (prj_all2 KsG p == Some KsL)
                  && (E.[? p]%fmap == Some (l_msg l_send q KsL)).
  Admitted.

  Lemma lookup_prjall lb Ks t (Gp : rg_ty) p KsL :
    (lookup lb Ks == Some (t, Gp)) ->
    (prj_all2 Ks p == Some KsL) ->
    exists L, (project2 Gp p == Some L) && (lookup lb KsL == Some (t, L)).
  Admitted.
*)
