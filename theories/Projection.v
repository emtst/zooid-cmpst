From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.AtomSets.
Require Import MPST.Forall.
Require Import MPST.Global.
Require Import MPST.Local.
Require Import MPST.Session.
Require Import MPST.Actions.

Section IProject.

  Open Scope mpst_scope.

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
      | Some s => Some (if s == s_var 0 then s_end else s_rec s)
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

  Fixpoint project (g : g_ty) (r : role) : option l_ty :=
    match g with
    | g_end => Some l_end
    | g_var v => Some (l_var v)
    | g_rec G =>
      match project G r with
      | Some L => Some (if L == l_var 0 then l_end else l_rec L)
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
      move: Lp_var Ih=>-> /(_ (l_var 0) 0); rewrite eq_refl/==>Ih.
      by apply: Ih.
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
    project (g_msg r s Ks) p == Some (l_var 0) ->
    r != p /\ s != p /\ r != s /\
    (forall K, member K Ks -> project K.cnt p == Some (l_var 0)).
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
  Proof.
    elim: Ks=>//= Kl Ks Ih in Ks' *.
    case Kl_p: partial_proj=>[s|//].
    case Ks_p: pprj_all=>[Ks0|//]; move: Ks_p=>/eqP/Ih-{Ih} Ih.
    move=>/eqP-[<-] K [E|/Ih-{Ih}[s' [M Kp]]]{Ks'}.
    - by move: E Kl_p=><- {Kl}; exists s; split=>//; left.
    - by exists s'; split=>//; right.
  Qed.

  Lemma pproj_var p q G Lq Sq :
    project G p == Some (l_var 0) ->
    project G q == Some Lq ->
    partial_proj Lq p == Some Sq ->
    Sq = s_var 0.
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

  Open Scope mpst_scope.
  Definition rlty_rel := rel2 rl_ty (fun=>rl_ty).
  Inductive EqL_ (r : rlty_rel) : rlty_rel :=
  | el_end : @EqL_ r rl_end rl_end
  | el_msg a p C1 C2 :
      same_dom C1 C1 ->
      R_all r C1 C2 ->
      @EqL_ r (rl_msg a p C1) (rl_msg a p C2).
  Hint Constructors EqL_.
  Definition EqL L1 L2 := paco2 EqL_ bot2 L1 L2.

  Lemma EqL_monotone : monotone2 EqL_.
  Proof.
    move=>L1 L2 r r' E H; elim: E=>[|a p C1 C2 D E]//; constructor=>//.
    by move: E; rewrite /R_all=>E L Ty G G' /E-{E}E /E/H.
  Qed.
  Hint Resolve EqL_monotone.

  Definition Merge (F : lbl /-> mty * rl_ty) (L : rl_ty) : Prop :=
    forall Lb Ty L', F Lb = Some (Ty, L') -> EqL L' L.

  Definition proj_rel := rel2 rg_ty (fun=>rl_ty).
  Inductive Proj_ (p : role) (r : proj_rel) : proj_rel :=
  | prj_end : @Proj_ p r rg_end rl_end
  | prj_send1 q KsG KsL :
      p != q ->
      R_all r KsG KsL ->
      @Proj_ p r (rg_msg None p q KsG) (rl_msg l_send q KsL)
  | prj_send2 l t q KsG KsL L :
      p != q ->
      R_all r KsG KsL ->
      KsL l = Some (t, L) ->
      @Proj_ p r (rg_msg (Some l) p q KsG) L
  | prj_recv o q KsG KsL :
      p != q ->
      R_all r KsG KsL ->
      @Proj_ p r (rg_msg o q p KsG) (rl_msg l_recv q KsL)
  | prj_mrg o q s KsG KsL L :
      q != s ->
      p != q ->
      p != s ->
      R_all r KsG KsL ->
      Merge KsL L ->
      @Proj_ p r (rg_msg o q s KsG) L
  .
  Hint Constructors Proj_.
  Lemma Proj_monotone p : monotone2 (Proj_ p).
  Proof.
  Admitted.
  Definition Project p CG CL := paco2 (Proj_ p) bot2 CG CL.

  Lemma project_rec G r L :
    project G r == Some L ->
    ((L == l_var 0) = false) ->
    project (g_rec G) r = Some (l_rec L).
  Proof. by move=>/=/eqP-[->] ->. Qed.

  Lemma gclosed_lclosed G r L :
    g_closed G ->
    project G r == Some L ->
    l_closed L.
  Proof.
    rewrite /g_closed/l_closed; elim/gty_ind1: G L 0 =>[|v|G Ih|p q Ks Ih] L n.
    - by move=> _ /eqP-[<-].
    - move=> /=; case: ifP; first by rewrite -cardfs_eq0 cardfs1.
      by move=> H _ /eqP-[<-]/=; rewrite H.
    - move: Ih=>/=; case Eq: (project G r) =>[Lr|//].
      move=> /(_ Lr n.+1)-Ih; move=>/Ih/(_ (eq_refl _)).
      by case: ifP=>// _ H /eqP-[<-].
    - rewrite project_msg=>H1.
      case Eq: (prj_all Ks r) => [Ks'|//]; case: ifP=>[//|p_neq_q]/=.
      move: Eq=>/eqP-Eq.
      case: ifP=>[p_eq_r /eqP-[<-]/=|p_neq_r].
      * rewrite !fsetUs_fset0 !member_map in H1 * => H1.
        move=> K M; move: (prjall_some2 Eq M)=>[G [M' /eqP-PrjG]].
        by apply: (Ih _ M'); first by rewrite H1 // H2.
      * case: ifP=>[q_eq_r /eqP-[<-]|q_neq_r /eqP].
        + rewrite !fsetUs_fset0 !member_map in H1 *=> H1 K M.
          move: (prjall_some2 Eq M) =>[G [M' /eqP-PrjG]].
          by apply: (Ih _ M'); first by rewrite H1 // H2.
        + case: Ks' Eq=>// Kl Ks' Eq /eqP/merge_some<- /=.
          case: Ks Eq Ih H1=>//= Kg Ks.
          case Eqg: (project Kg.2.2 r)=>[Lk|//].
          case EqKs: (prj_all Ks r)=>[Ks''|//].
          rewrite !fsetUs_list => /eqP-[[<- H2]] Ih /andP-[H3 H4].
          by apply: (Ih Kg)=>//=; [left|apply/eqP].
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
    - by case: project; case: prj_all.
    - move=> H. move: (H K (or_introl erefl)).
      case: project =>// L /(_ L (eq_refl _))->.
      move: H=>/(_ _ (or_intror _))-H; move: Ih => /(_ _ H) {H}.
      by case: prj_all => [Ksr|//] /(_ Ksr erefl)-> [<-<-]/=.
  Qed.

  (*
  Lemma projclosed_rec G r L :
    project G r == Some L ->
    g_closed (g_rec G) ->
    ((L == l_var (bv _ 0)) = false) ->
    project (g_open 0 (g_rec G) G) r = Some (l_open 0 (l_rec L) L).
  Proof.
    move=> H C L0; move: (project_rec H L0) => Hr; move: 0 {L0} (g_rec G) C (l_rec L) Hr.
    elim/gty_ind1: G =>[|v|G Ih|p q Ks Ih] in L H *.
    - by move: H=>/eqP-[<-].
    - move: H =>/eqP-[<-] /= n G' C L'.
      by case: v G' C=>//= m; case: ifP.
    - move: H Ih=>/=.
      move:Ih=>/=; case Eq:project=>[Lr|//=].
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
  *)

  Inductive In : role -> rg_ty -> Prop :=
  | In_here r a p q Ks :
      (r == p) || (r == q) ->
      In r (rg_msg a p q Ks)
  | In_msg r a p q Ks :
      (exists Lb Ty L, Ks Lb = Some (Ty, L) /\ In r L) ->
      In r (rg_msg a p q Ks)
  .
  Lemma In_ind1 :
    forall P : role -> rg_ty -> Prop,
      (forall r a p q C, (r == p) || (r == q) -> P r (rg_msg a p q C)) ->
      (forall r a p q C,
          (exists Lb Ty L, C Lb = Some (Ty, L) /\ In r L /\ P r L) -> P r (rg_msg a p q C)) ->
      forall (s : role) (r : rg_ty), In s r -> P s r.
  Proof.
  Admitted.

  Lemma notin_part_g_open_strong d r G G': r \notin participants G ->
    r \notin participants G'-> r \notin participants (g_open d G' G).
  Proof.
  move=> h1 rnG'; move: h1; apply: contra; elim/gty_ind1: G d.
  + rewrite //=.
  + rewrite //= => v d.
    by case: ifP=>[_ F|//]; rewrite F in rnG'.
  + rewrite //=. by move=> G ih d; apply ih.
  + move=>p q Ks ih d. rewrite /= !in_cons -map_comp/comp/=.
    move=>/orP-[->//|/orP-[->|]]; first by rewrite orbC.
    move=> H.
    do ! (apply/orP; right).
    move: H=>/flatten_mapP-[K inKs inK].
    apply/flatten_mapP.
    exists K=>//.
    by apply: (ih _ _ d); first by apply/memberP.
  Qed.

  Lemma same_notin_part_g_open d r G G': participants G' = participants G ->
    r \notin participants G -> r \notin participants (g_open d G' G).
  Proof.
  move=> hp1 hp2; apply: notin_part_g_open_strong; [by apply hp2 | by rewrite hp1 //=].
  Qed.

  Lemma notin_part_g_open r G:
    r \notin participants G -> r \notin participants (g_open 0 (g_rec G) G).
  Proof.
  by apply same_notin_part_g_open; rewrite //=.
  Qed.

  Lemma r_in_unroll r G n:
    r \in participants (n_unroll n G) -> r \in participants G.
  Proof.
  apply: contraLR.
  (*move: {-2}(rec_depth G) (erefl (rec_depth G)) => n.*)
  elim: n => [rewrite //= | n ih] in G *; case G; rewrite //=.
  move=> G0 notinpart; apply ih.
  unfold unroll; apply notin_part_g_open; by [].
  Qed.

  Lemma r_in_unroll_rec_depth r G:
    r \in participants (n_unroll (rec_depth G) G) -> r \in participants G.
  Proof. by apply r_in_unroll. Qed.

  (* FIXME: refactor somewhere else *)
  Lemma gen2 A B (x' : A) (y' : B) Q P :
    (forall x y, Q x y -> x = x' -> y = y' -> P) ->
    Q x' y' -> P.
  Proof. by move=>H /H/( _ erefl erefl).  Qed.

  Lemma r_in_unroll_msg r G a p q Ks :
    GUnroll G (rg_msg a p q Ks) ->
    guarded 0 G ->
    g_closed G ->
    (r == p) || (r == q) ->
    r \in participants G.
  Proof.
    move=> GU GG CG r_pq; apply/(r_in_unroll_rec_depth).
    move: (unroll_guarded CG GG) r_pq => H.
    move: GU=>/(GUnroll_ind (rec_depth G)); move: H.
    move: (n_unroll _ G) => [|v|G'|p' q' Ks'].
    - by move=>_; apply: gen2=>iG cG /gunroll_unfold-[].
    - by move=>_; apply: gen2=>iG cG /gunroll_unfold-[].
    - by move=>/(_ G')/eqP.
    - move=>_; apply: gen2=>iG cG /gunroll_unfold-[]//.
      move=> p'' q'' Ks'' CC GU E; move: E GU=> [->->->]{p'' q'' Ks''} GU.
      by move=>[_->-> _]/=; rewrite !in_cons orbA =>->.
  Qed.

  (* FIXME: refactor into correct place *)
  Lemma g_closed_unroll n iG : g_closed iG -> g_closed (n_unroll n iG).
  Proof. by elim: n iG=>[|n Ih]//=; case=>//= iG /gopen_closed/Ih. Qed.

  (* FIXME: refactor into correct place *)
  Lemma g_guarded_unroll iG :
    g_closed (g_rec iG) -> guarded 0 (g_rec iG) -> guarded 0 (unroll iG).
  Proof.
    move=> C GG; have GG': (guarded 1 iG) by move:GG C=>/=; case: iG.
    by move: (guarded_open 0 GG C GG')=>/guarded_depth_gt/(_ (gopen_closed C)).
  Qed.

  (* FIXME: refactor into correct place *)
  Lemma g_guarded_nunroll n iG
    : g_closed iG -> guarded 0 iG -> guarded 0 (n_unroll n iG).
  Proof.
    elim: n iG=>[|n Ih]//;case=>// iG CG /(g_guarded_unroll CG)/Ih-H/=.
    by apply/H/gopen_closed.
  Qed.

  (* FIXME: refactor into correct place *)
  Lemma l_guarded_unroll n iL :
    l_closed iL -> lguarded 0 iL -> lguarded 0 (lunroll n iL).
  Proof.
  Admitted.

  Lemma l_closed_unroll n iL :
    l_closed iL -> l_closed (lunroll n iL).
  Proof.
  Admitted.

  Lemma notin_unroll r iG cG :
    g_closed iG ->
    guarded 0 iG ->
    r \notin participants iG ->
    GUnroll iG cG ->
    ~ In r cG.
  Proof.
    move=>H1 H2 H3 H4 H5; move: H5 iG H1 H2 H3 H4.
    elim/In_ind1.
    - move=> r0 a p q C E iG CiG GiG r0_iG.

      (* FIXME, avoid repetition below *)
      move/(GUnroll_ind (rec_depth iG)).
      move: (contra (fun b => r_in_unroll (n:=rec_depth iG) b) r0_iG).
      move: (g_guarded_nunroll (rec_depth iG) CiG GiG).
      move: (unroll_guarded CiG GiG) (g_closed_unroll (rec_depth iG) CiG).
      move: (n_unroll (rec_depth iG) iG) => {iG CiG GiG r0_iG} iG H CG GG r0G.
      move=>/gunroll_unfold-U.
      case CE: _/ U H CG GG r0G=>[|IG CG _| F T iC cC U]//; first by move=>/(_ IG)/eqP.
      (* FIXME, avoid repetition above *)

      move: CE U => [_ <-<-<-] {F T cC a} _ _ _ _.
      by rewrite !in_cons orbA negb_or=>/andP-[H _]; move: E H=>->.
    - move=>r0 a p q C [Lb [Ty [L [E [In_L Ih]]]]] iG CiG GiG r0_iG.

      (* FIXME, avoid repetition below *)
      move/(GUnroll_ind (rec_depth iG)).
      move: (contra (fun b => r_in_unroll (n:=rec_depth iG) b) r0_iG).
      move: (g_guarded_nunroll (rec_depth iG) CiG GiG).
      move: (unroll_guarded CiG GiG) (g_closed_unroll (rec_depth iG) CiG).
      move: (n_unroll (rec_depth iG) iG) => {iG CiG GiG r0_iG} iG H CG GG r0G.
      move=>/gunroll_unfold-U.
      case CE: _/ U H CG GG r0G=>[|IG CG _| F T iC cC U]//; first by move=>/(_ IG)/eqP.
      (* FIXME, avoid repetition above *)

      move: CE U=>[_<-<-<-] {F T cC a} U _; rewrite/g_closed/=.
      elim: U E=>// Lb0 Ty0 IG CG iC0 cC0 [U|//] UA IhC.
      move=>E; rewrite fsetUs_list -/(g_closed _).
      move=>/=/andP-[CIG CC0] /andP-[GIG GC0].
      do ! (rewrite ?in_cons ?mem_cat negb_or).
      rewrite !andbA=>/andP-[/andP-[N H] F] .
      move: E; rewrite /extend; case: ifP=>[/eqP|_ /IhC/(_ CC0 GC0)-HF].
      * by move=> _ E; move: E U=>[_ ->]; apply: Ih.
      * by apply: HF; do ! (rewrite in_cons negb_or); rewrite andbA N F.
  Qed.

  (* FIXME: refactor lemmas below *)
  Lemma project_closed r iG iL :
    g_closed iG ->
    project iG r == Some iL ->
    l_closed iL.
  Proof.
    rewrite /l_closed.
  Admitted.

  Lemma project_guarded r iG iL :
    guarded 0 iG ->
    project iG r == Some iL ->
    lguarded 0 iL.
  Proof.
    rewrite /l_closed.
  Admitted.

  Lemma lunroll_end cL :
    LUnroll l_end cL -> cL = rl_end.
  Proof. by move=> /lu_unfold-LU; case Eq: _ _ / LU. Qed.

  Lemma notin_project_end r G :
    ~ In r G -> Project r G rl_end.
  Proof.
  (* move: G; cofix Ch => G H. *)
  (* case r_eq_r': r G / H => [r'|r' a p q Ks r_ne_p r_ne_q Ks_r]. *)
  (* - by constructor. *)
  (* - apply/(prj_mrg (L:=rl_end) (KsL:=map (fun K => (K.1, (K.2.1, rl_end))) Ks) _ _ r_ne_p r_ne_q). *)
  (*   admit. *)
  (*   rewrite -r_eq_r' in r_ne_p r_ne_q Ks_r * => {r' r_eq_r'}. *)
  (*   move: Ks Ks_r; cofix Ch'; case. *)
  (*   - by constructor. *)
  (*   - move=> K Ks. *)
  (*     move: {-1}r (erefl r) {-1}(K::Ks) (erefl (K::Ks))=>r' rr' Ks' EKs' H. *)
  (*     move: H rr' EKs'. *)
  (*     case=>// r0 K0 Ks0 H0 H1 rr0 [KK0 KKs0]. *)
  (*     move: rr0 KK0 KKs0 H0 H1=><-<-<- {r0 K0 Ks0} H0 H1. *)
  (*     case: K H0 => l [t G]//= H0. *)
  (*     move: (Ch' _ H1)=>H2. *)
  (*     move: (Ch _ H0)=> H3. *)
  (*     by constructor. *)
  Admitted.

  Lemma project_unroll G r L :
    project G r == Some L ->
    g_closed G ->
    project (n_unroll (rec_depth G) G) r
    = Some (lunroll (rec_depth G) L).
  Admitted.

  Lemma EqL_refl CL : EqL CL CL.
  Admitted.
  Hint Resolve EqL_refl.

  (* FIXME: abstract all g_closed && guarded ... as "wf" to simplify statements
   *)

  Lemma cproj_all (r0 : proj_rel) FROM CONT CC KsL C
        (CIH : forall iG iL cG cL,
            g_closed iG ->
            guarded 0 iG ->
            project iG FROM == Some iL ->
            GUnroll iG cG ->
            LUnroll iL cL ->
            r0 cG cL)
        (cG : forall x, member x CONT -> g_fidx 0 x.cnt == fset0)
        (gG : forall x, member x CONT -> guarded 0 x.cnt)
        (GU : @unroll_all (upaco2 g_unroll bot2) CONT CC)
        (LU : l_unroll_all (upaco2 l_unroll bot2) KsL C)
        (PRJ : prj_all CONT FROM = Some KsL)
    : R_all (upaco2 (Proj_ FROM) r0) CC C.
  Proof.
    rewrite /R_all=> Lb Ty G G' CC_Lb C_Lb.
    right.
  Admitted.

  Lemma lunroll_merge r L CL CONT Ks
        (LU : LUnroll L CL)
        (PRJ : prj_all CONT r = Some Ks)
        (MRG : merge L [seq K.cnt | K <- Ks] = Some L)
    : exists CCL, l_unroll_all (upaco2 l_unroll bot2) Ks CCL /\
                  Merge CCL CL.
  Proof.
    elim: CONT Ks MRG PRJ =>[|K' KS' Ih] Ks M//=.
    - by move=>[<-]; exists (empty _); split=>//; apply: lu_nil.
    - case: project=>// L'; case P: prj_all=>[Ks1|]//.
      move=> E; move:E M=>[<-]/=; case: ifP=>[/eqP-> M|]// {Ks}.
      move: (Ih _ M P)=>[CCL [U_all M']].
      exists (extend K'.lbl (K'.mty, CL) CCL); split.
      + by apply: lu_cons =>//; left.
      + move=> Lb Ty {L'}L'; rewrite/extend; case:ifP=>[|_ /M']//.
        by move=> _ [_ <-].
  Qed.

  Lemma project_nonrec (r0 : proj_rel ) r CL CG L G
        (CIH : forall iG iL cG cL,
            g_closed iG ->
            guarded 0 iG ->
            project iG r == Some iL ->
            GUnroll iG cG ->
            LUnroll iL cL ->
            r0 cG cL)
        (cL : l_closed L)
        (gL : lguarded 0 L)
        (cG : g_closed G)
        (gG : guarded 0 G)
        (nrG : forall G' : g_ty, G != g_rec G')
        (iPrj : project G r = Some L)
        (GU : GUnroll G CG)
        (LU : LUnroll L CL)
    : paco2 (Proj_ r) r0 CG CL.
  Proof.
    move: (closed_not_var cG).
    case: G cG gG nrG iPrj GU=>[|V _ _ _ _ _ /(_ V)/eqP|GT _ _ /(_ GT)/eqP|]//.
    - move=> _ _ _ [E]; move: E LU=><- /lu_unfold-LU /gunroll_unfold-GU _. (* FIXME: naming consistency *)
      case Eq: _ _ / GU =>//; move => {Eq}.
      case Eq: _ _ / LU =>//; move => {Eq}.
      by apply: paco2_fold.
    - move=>FROM TO CONT; rewrite project_msg /g_closed/=.
      move=>/fsetUs_fset0/member_map-cG /forallbP/forall_member-gG _ I_prj GU _.
      move: GU; move=>/gunroll_unfold.
      case E: _ _/ =>// [FROM' TO' CONT' CC GU].
      move: E GU=> [<-<-<-] {FROM' TO' CONT'} GU.
      apply/paco2_fold; move: I_prj.
      case E: prj_all=>[KsL|]//; case:ifP=>// F_neq_T.
      case:ifP=>[F_r | F_ne_r].
      + move=>[EL]; move: EL cL gL LU=><- {L} cL gL /lu_unfold-LU.
        case EL: _ _/LU=>[||a p Ks C LU]//; move: EL LU=>[<-<-<-] LU {a p Ks}.
        move: F_r CIH E=>/eqP<-{r} CIH E; apply/prj_send1; first by apply/negPf.
        apply/(cproj_all CIH cG gG GU LU)=>//.
      + case:ifP=>[T_r | T_ne_r].
        * move=>[EL]; move: EL cL gL LU=><- {L} cL gL /lu_unfold-LU {F_ne_r}.
          case EL: _ _/LU=>[||a p Ks C LU]//; move: EL LU=>[<-<-<-] LU {a p Ks}.
          move: T_r CIH E=>/eqP<-{r} CIH E.
          apply/prj_recv; first by rewrite eq_sym (F_neq_T).
          by apply/(cproj_all CIH cG gG GU LU)=>//.
        * move=> M.
          have {M}M: merge L [seq K.cnt | K <- KsL] = Some L
            by move: M=>{E}; case: KsL=>//=K Ks /eqP-M;
               move: (merge_some M)=>E; move: E M=>->; rewrite eq_refl=>/eqP.
          move: (lunroll_merge LU E M)=>[CCL [{LU}LU MRG]].
          move: F_ne_r T_ne_r; rewrite eq_sym=>F_ne_r; rewrite eq_sym=>T_ne_r.
          apply: prj_mrg;rewrite ?F_ne_r ?T_ne_r ?F_neq_T//; last by apply:MRG.
          by apply/(cproj_all CIH cG gG GU LU)=>//.
  Qed.

  Lemma ic_proj r :
    forall iG iL cG cL,
    g_closed iG ->
    guarded 0 iG ->
    project iG r == Some iL ->
    GUnroll iG cG ->
    LUnroll iL cL ->
    Project r cG cL.
  Proof.
    pcofix CIh.
    move=> iG iL cG cL ciG giG iGiL GU LU.
    move: (project_closed ciG iGiL) => ciL.
    move: (project_guarded giG iGiL) => giL.
    move : GU (unroll_guarded ciG giG)=>/(GUnroll_ind (rec_depth iG))=>GU nrG.
    move: LU =>/(LUnroll_ind (rec_depth iG))=>LU.
    move: (project_unroll iGiL ciG) => proj.
    move: (g_guarded_nunroll (rec_depth iG) ciG giG)=>guiG.
    move: (g_closed_unroll (rec_depth iG) ciG)=>cuiG.
    move=> {ciG giG iGiL}.
    move: (l_guarded_unroll (rec_depth iG) ciL giL)=>guiL.
    move: (l_closed_unroll (rec_depth iG) ciL)=>cuiL.
    move=>{ciL giL}.
    by apply/(project_nonrec CIh cuiL) =>//.
  Qed.

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
