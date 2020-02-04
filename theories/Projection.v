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

  Fixpoint s_binds d s :=
    match s with
    | s_var v => v == d
    | s_rec s => s_binds d.+1 s
    | _ => false
    end.

  Fixpoint s_isend s :=
    match s with
    | s_end => true
    | s_rec s => s_isend s
    | _ => false
    end.

  Fixpoint partial_proj (l : l_ty) (r : role) : option s_ty :=
    match l with
    | l_end => Some (s_end)
    | l_var v => Some (s_var v)
    | l_rec L =>
      match partial_proj L r with
      | Some s => Some (if s_binds 0 s then s_end else s_rec s)
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

  (* Lemma lguarded_next L n m *)
  (*   : lguarded m L -> (forall s, s <= n -> ~~ l_binds n L) -> lguarded n (l_rec L). *)

  Fixpoint project (g : g_ty) (r : role) : option l_ty :=
    match g with
    | g_end => Some l_end
    | g_var v => Some (l_var v)
    | g_rec G =>
      match project G r with
      | Some L => Some (if l_binds 0 L then l_end else l_rec L)
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
    case Kp: project => [Lp|//].
    case Ksp: prj_all => [LKs|//]; move: Ksp=>/eqP-Ksp.
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
    case Kgp: project => [Lp|//].
    case Ksp: prj_all => [Ks''|//]; move: Ksp=>/eqP-Ksp.
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
    (forall (s s0 : seq (lbl * (mty * s_ty))),
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
    case Kspq: pprj_all => [Ks0'|//].
    case Ksqp: pprj_all => [Ks1'|//].
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

  Lemma mergeall_fun (A B : eqType) (f : A -> B) (Ks : seq (lbl * (mty * A))) X:
    merge_all [seq x.cnt | x <- Ks] == Some X 
    -> merge_all [seq f x.cnt | x <- Ks] == Some (f X).
  Proof.
    case: Ks=>[//|K Ks/=]; elim: Ks=>[|K' Ks]//=.
    - by move=>/eqP-[->].
    - by move=> Ih; case: ifP=>///eqP-[->]; rewrite eq_refl=>/Ih.
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
    case Kspq: pprj_all => [Ks0'|//]; move => EqS.
    case Ksqp: merge_all => [L'|//].
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
    case Kspq: pprj_all => [Ks0'|//].
    case Ksqp: merge_all => [L'|//].
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
      case Kp: project =>[Lp|]//; case Ksp: prj_all =>[Lsp|]//=.
      case Ep: partial_proj =>[Sp|]//; case Esp: pprj_all =>[Ssp|]//=.
      case Kq: project =>[Lq|]//; case Ksq: prj_all=>[Lsq|]//=.
      case Eq: partial_proj=>[Sq|]//; case Esq: pprj_all=>[Ssq|]//=.
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

  Lemma notin_flatten (A: eqType) (p : A) Ks :
    (forall K, member K Ks -> p \notin K) ->
    p \notin flatten Ks.
  Proof.
    elim: Ks=>//=K Ks Ih H; rewrite mem_cat negb_or (H _ (or_introl erefl)) Ih//.
    by move=> K0 M; apply/H; right.
  Qed.

  Lemma l_binds_notin Lp p G
        (Ep : project G p = Some Lp)
        (BLp : l_binds 0 Lp)
    : p \notin participants G.
  Proof.
    elim/gty_ind1: G 0 =>[|v|G Ih|q r Ks Ih] n//= in Lp BLp Ep *.
    - move: Ep Ih; case Prj: project=>[L|//]; move: Prj=>/eqP-Prj; case: ifP.
      + move=> B [E]; move: E BLp=><- _.
        by move=>/(_ _ _ B erefl).
      + by move=>_ [E]; move: E BLp=><-/= BLp /(_ _ _ BLp erefl).
    - move: Ep; move: (project_msg q r Ks p)=>/=->.
      case Prj: prj_all=>[Ks'|//]; case: ifP=>// Eqr.
      case: ifP=>Eqp; first by move=> [E]; move: E BLp=><-.
      case: ifP=>Erp; first by move=> [E]; move: E BLp=><-.
      rewrite !in_cons eq_sym Eqp eq_sym Erp /==>M.
      apply/notin_flatten/member_map=> K Mm; apply/(Ih _ Mm _ _ BLp).
      by move: Prj M=>/eqP-Prj /eqP-M; move: (prjall_merge Prj M)=>/(_ _ Mm)/eqP.
  Qed.

  Lemma project_var_notin p G v L :
    (L == l_end) || (L == l_var v) ->
    project G p == Some L ->
    p \notin participants G.
  Proof.
    elim/gty_ind1: G => [|v'|G Ih|q r Ks Ih]// in L v *.
    - move: Ih=>/=; case Prj: project =>[Lp|//] Ih.
      move=>/orP-[/eqP->|/eqP->]; case: ifP=>[Lp_var|]//.
      by move: (l_binds_notin Prj Lp_var).
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

  Lemma projectmsg_var n p r s Ks :
    project (g_msg r s Ks) p == Some (l_var n) ->
    r != p /\ s != p /\ r != s /\
    (forall K, member K Ks -> project K.cnt p == Some (l_var n)).
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

  Lemma pproj_var n p q G Lq Sq :
    project G p == Some (l_var n) ->
    project G q == Some Lq ->
    partial_proj Lq p == Some Sq ->
    Sq = s_var n.
  Proof.
    elim/gty_ind1: G =>[//|v//=|G Ih//=|r s Ks Ih] in Lq Sq *.
    - by move=>/eqP-[->]/eqP-[<-]/=/eqP-[<-].
    - by case: project=>//[[]]//v'; case: ifP.
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

  Lemma proj_var_eq G p q v v':
    project G p == Some (l_var v) ->
    project G q == Some (l_var v') ->
    v == v'.
  Proof.
    elim/gty_ind1: G => [|n|G Ih|f t Ks Ih]// in v v' *.
    - by move=>/eqP-[<-]/eqP-[<-].
    - move=>/=.
      case Pp: project =>[Lp|//]; move: Pp=>/eqP=>Pp.
      case Pq: project =>[Lq|//]; move: Pq=>/eqP=>Pq.
      by case: ifP.
    - rewrite !project_msg.
      case Pp: prj_all =>[Lp|//]; move: Pp=>/eqP=>Pp.
      case Pq: prj_all =>[Lq|//]; move: Pq=>/eqP=>Pq.
      case: ifP=>//f_ne_t; do ! case: ifP=>//.
      move=> t_ne_q f_ne_q t_ne_p f_ne_p.
      case: Ks Pp Pq Ih=>[//= /eqP-[<-] /eqP-[<-]//|K Ks/=].
      case Pp: project =>[Lpp|//]; move: Pp=>/eqP=>Pp.
      case Pq: project =>[Lqq|//]; move: Pq=>/eqP=>Pq.
      case Pp': prj_all =>[Lp'|//]; move: Pp'=>/eqP=>Pp'.
      case Pq': prj_all =>[Lq'|//]; move: Pq'=>/eqP=>Pq'.
      move=>/eqP-[<-]/eqP-[<-].
      move=> /(_ K (or_introl erefl))-Ih.
      move=>/merge_some-Ep /merge_some-Eq; move: Ep Eq Pp Pq=>/=->->.
      by apply: Ih.
  Qed.

  Lemma sty_not_var A G (b1 : nat -> A) (b2 : A) :
    (forall v : nat, G != s_var v) ->
    match G with | s_var v => b1 v | _ => b2 end = b2.
  Proof. by case: G =>[|n /(_ n)/eqP||]. Qed.

  Lemma dual_not_var G :
    (forall v : nat, G != s_var v) ->
    (forall v : nat, dual G != s_var v).
  Proof. by case: G=>//. Qed.

  Lemma flatten_notin (A: eqType) (p : A) Ks :
    p \notin flatten Ks ->
    (forall K, member K Ks -> p \notin K).
  Proof.
    elim: Ks=>//=K Ks Ih; rewrite mem_cat negb_or=>/andP-[pK pKs] K' [->//|].
    by move: K'; apply/Ih.
  Qed.

  (* Lemma notin_parts_project Lp p G *)
  (*       (Ep : project G p = Some Lp) *)
  (*       (NIN : p \notin participants G) *)
  (*   : p \notin partsL Lp. *)
  (* Proof. *)
  (*   elim/gty_ind1: G=>[|v|G Ih|q r Ks Ih] in Lp NIN Ep *; move: Ep=>[]. *)
  (*   - by move<-. *)
  (*   - by move<-. *)
  (*   - move=>/=; case Ep: project=>[Lp'|//]; case: ifP=>//; first by move=>_[<-]. *)
  (*     by move=> _ [<-]/=; apply/Ih. *)
  (*   - rewrite project_msg; case Ep:prj_all=>[Ks'|//]; case:ifP=>//Npq. *)
  (*     move: NIN=>/=; rewrite !in_cons !negb_or=>/andP-[N1 /andP-[N2 NIN]]. *)
  (*     rewrite eq_sym (negPf N1) eq_sym (negPf N2) => M. *)
  (*     have [K MK]: (exists K, member K Ks). *)
  (*     + case: Ks Ep {Ih NIN}=>[[E]|K Ks _]//=; last (by exists K; left). *)
  (*       by move: E M=><-. *)
  (*     move: Ep M=>/eqP-Ep /eqP-M; move: (prjall_merge Ep M)=>H. *)
  (*     move: NIN=>/flatten_notin/member_map-H' {Ep M N1 N2 Npq Ks'}. *)
  (*     by apply/(Ih _ MK); first (by apply/H'); apply/eqP/H. *)
  (* Qed. *)

  (* Lemma binds_project_isin n G L p : *)
  (*   project G p = Some L -> *)
  (*   l_binds n L -> *)
  (*   0 \in g_fidx n G. *)
  (* Proof. *)
  (*   elim/gty_ind1: G=>[|v|G Ih|q r Ks Ih] in L *. *)
  (*   - by move=>[<-]. *)
  (*   - move=>[<-]/=. *)
  (*   (* - by move=>[<-]; case: v=>//= _; apply/fset11.  *) *)
  (*   - move=>/=; case Ep: project=>[Lp|//] [<-]//=. *)
  (*     case: ifP=>//=. *)
  (*     case: Lp Ep=>//=[v|L']. *)
  (*     admit. *)
  (*     case: L'=>//=[v|L']. *)

  (* Lq : l_ty *)
  (* Eq : project G q = Some Lq *)
  (* Sq : s_ty *)
  (* Eqp : partial_proj Lq p = Some Sq *)
  (* ============================ *)
  (* l_binds 0 Lq = false -> *)
  (* l_binds 0 Lp -> *)

  (* Lemma sbinds_lt m n S : s_binds n S -> n <= m -> s_binds m S. *)
  (* Proof. *)
  (*   elim/sty_ind: S=>[|v|S Ih|a Ks Ih]//= in n m *. *)
  (*   - by move/leq_trans=> H /H. *)
  (*   - by move/Ih=>H Le; apply/H. *)
  (* Qed. *)

  Lemma pproj_sbinds n L p S
        (BL : l_binds n L)
        (PRJ : partial_proj L p = Some S)
    : s_isend S || s_binds n S.
  Proof.
    elim/lty_ind2: L=>[|v|L Ih|a q Ks Ih]//= in n S BL PRJ *.
    - by move: PRJ=>[<-]; rewrite /= BL.
    - move: PRJ; case PRJ:partial_proj =>[S'|//] [<-{S}].
      move: (Ih _ _ BL PRJ)=>/orP-[END|BND]; case: ifP=>//=.
      + by rewrite END.
      + by rewrite orbC BND.
  Qed.

  Lemma prjall_merge_cons Ks p KsL L :
    prj_all Ks p = Some KsL ->
    merge_all [seq K.cnt | K <- KsL] = Some L ->
    exists K, member K Ks.
  Proof.
    case: Ks=>//=; first by move=>[<-].
    move=> K Ks; case Prj:project=>[L'|//]; case PrjA:prj_all=>[KL'|//].
    by move=>_ _; exists K; left.
  Qed.

  Lemma project_binds_eq p q G Lp Lq n m :
    project G p = Some Lp ->
    project G q = Some Lq ->
    l_binds n Lp ->
    l_binds m Lq ->
    l_binds n Lq.
  Proof.
    elim/gty_ind1: G=>[|v|G Ih|r s Ks Ih] in Lp Lq n m *.
    - by move=>[<-].
    - by move=>[<-] [<-]/=.
    - move=>/=; case Pp: project=>[Lp'|//]; case Pq: project=>[Lq'|//].
      by case: ifP=>_ [<-]//; case: ifP=>_ [<-]//=; apply/Ih.
    - rewrite !project_msg.
      case PRJp: prj_all=>[KSp|//]; case PRJq: prj_all=>[KSq|//].
      case: ifP=>// Ers; do ! (case: ifP=> _; first by move=>[<-]).
      move=>MRGp;do ! (case: ifP=> _; first by move=>[<-]).
      move=> MRGq; case: (prjall_merge_cons PRJp MRGp) =>[K M].
      move: PRJq MRGq=>/eqP-Pq /eqP-Mq; move: (prjall_merge Pq Mq M)=>/eqP.
      move: PRJp MRGp=>/eqP-Pp /eqP-Mp; move: (prjall_merge Pp Mp M)=>/eqP.
      move: K M Lp Lq n m {Mq Mp Pp Pq Ers KSp KSq}; apply/Ih.
  Qed.

  Lemma sbinds_eq n m S :
    s_binds n S -> s_binds m S -> n = m.
  Proof.
    elim/sty_ind: S=>[|v|S Ih|a Ks Ih]//= in n m *.
    - by move=>/eqP->/eqP.
    - by move=> H1 H2; move: (Ih _ _ H1 H2)=>[].
  Qed.

  Lemma pproj_notin_binds n G Lp Lq p q S
        (PRJp : project G p = Some Lp)
        (BLp : l_binds n Lp)
        (PRJq : project G q = Some Lq)
        (PPRJ : partial_proj Lq p = Some S)
    : s_binds n S.
  Proof.
    elim/gty_ind1: G=>[|v|G Ih|r s Ks Ih] in n S Lp Lq PPRJ BLp PRJp PRJq *.
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

  Lemma sbinds_dual n S : s_binds n S = s_binds n (dual S).
  Proof. by elim/sty_ind: S=>[|v|S Ih|a Ks Ih]//= in n *; apply/Ih. Qed.

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
  Definition rlty_rel := rl_ty -> rl_ty -> Prop.
  Inductive EqL_ (r : rlty_rel) : rlty_rel :=
  | el_end : @EqL_ r rl_end rl_end
  | el_msg a p C1 C2 :
      same_dom C1 C2 ->
      R_all r C1 C2 ->
      @EqL_ r (rl_msg a p C1) (rl_msg a p C2).
  Hint Constructors EqL_.
  Definition EqL L1 L2 := paco2 EqL_ bot2 L1 L2.

  Lemma EqL_monotone : monotone2 EqL_.
  Proof.
    move=>L1 L2 r r' E H; elim: E =>[|a p C1 C2 D E]//; constructor=>//.
    by move: E; rewrite /R_all=>E L Ty G G' /E-{E}E /E/H.
  Qed.
  Hint Resolve EqL_monotone.

  Definition Merge (F : lbl /-> mty * rl_ty) (L : rl_ty) : Prop :=
    forall Lb Ty L', F Lb = Some (Ty, L') -> EqL L' L.

  Definition proj_rel := rg_ty -> rl_ty -> Prop.
  Inductive Proj_ (p : role) (r : proj_rel) : proj_rel :=
  | prj_end : Proj_ p r rg_end rl_end
  | prj_send1 q KsG KsL :
      p != q ->
      R_all r KsG KsL ->
      Proj_ p r (rg_msg None p q KsG) (rl_msg l_send q KsL)
  | prj_send2 l t q KsG KsL L :
      p != q ->
      R_all r KsG KsL ->
      KsL l = Some (t, L) ->
      Proj_ p r (rg_msg (Some l) p q KsG) L
  | prj_recv o q KsG KsL :
      p != q ->
      R_all r KsG KsL ->
      Proj_ p r (rg_msg o q p KsG) (rl_msg l_recv q KsL)
  (* | prj_end2 G : ~ In r G -> Proj_ r G rl_end *)
  | prj_mrg o q s KsG KsL L :
      q != s ->
      p != q ->
      p != s ->
      (* InAll r KsG -> *)
      R_all r KsG KsL ->
      Merge KsL L ->
      Proj_ p r (rg_msg o q s KsG) L
  .
  Hint Constructors Proj_.
  Lemma Proj_monotone p : monotone2 (Proj_ p).
  Proof.
  rewrite /monotone2; move=> x0 x1 r r' it LE; move: it; case=>//.
  + move=> q KsG KsL neq HP; constructor =>//; move: HP; rewrite /R_all.
    move=> HP l Ty G L KsG_l KsL_l; apply: LE; by apply: (@HP l Ty G L KsG_l KsL_l).
  + move=> l t q KsG KsL L neq HP KsL_l; apply: (@prj_send2 _ _ l t _ _ KsL) => //.
    move: HP; rewrite /R_all; move=> HP l0 t0 G0 L0 KsG_l0 KsL_l0; apply LE.
    by apply: (@HP l0 _ _ _ KsG_l0 KsL_l0).
  + move=> o q KsG KsL neq HP; constructor =>//; move: HP; rewrite /R_all.
    move=> HP l t G L KsG_l KsL_l; apply: LE. by apply: (HP _ _ _ _ KsG_l KsL_l).
  + move=> o q s KsG KsL L0 neq_qs neq_pq neq_ps HP merg.
    apply (@prj_mrg _ _ _ _ _ KsG KsL _) =>//; move: HP; rewrite /R_all.
    move=> HP l t G L KsG_l KsL_l; apply: LE; by apply: (HP _ _ _ _ KsG_l KsL_l).
  Qed.
  Definition Project p CG CL := paco2 (Proj_ p) bot2 CG CL.

  Lemma gclosed_lclosed d G r L :
    g_fidx d G == fset0 ->
    project G r == Some L ->
    l_fidx d L == fset0.
  Proof.
    elim/gty_ind1: G =>[|v|G Ih|p q Ks Ih] in d L *.
    - by move=> _ /eqP-[<-].
    - move=> /=; case: ifP; first by rewrite -cardfs_eq0 cardfs1.
      by move=> H _ /eqP-[<-]/=; rewrite H.
    - move: Ih=>/=; case Eq: project =>[Lr|//]; move: Eq=>/eqP-Eq.
      move=> /(_ d.+1 Lr)-Ih /Ih/(_ (eq_refl _))-H.
      case: ifP=>//; first by move=> _ /eqP-[<-].
      by move=>B /eqP-[<-]/=; apply/H.
    - rewrite project_msg=>H1.
      case Eq: prj_all => [Ks'|//]; case: ifP=>[//|p_neq_q]/=.
      move: Eq=>/eqP-Eq.
      case: ifP=>[p_eq_r /eqP-[<-]/=|p_neq_r].
      * rewrite !fsetUs_fset0 !member_map in H1 * => H1.
        move=> K M; move: (prjall_some2 Eq M)=>[G [M' /eqP-PrjG]].
        by apply: (Ih _ M'); first (by rewrite H1 // H2); apply: PrjG.
      * case: ifP=>[q_eq_r /eqP-[<-]|q_neq_r /eqP].
        + rewrite !fsetUs_fset0 !member_map in H1 *=> H1 K M.
          move: (prjall_some2 Eq M) =>[G [M' /eqP-PrjG]].
          by apply: (Ih _ M'); first (by rewrite H1 // H2); apply: PrjG.
        + case: Ks' Eq=>// Kl Ks' Eq /eqP/merge_some<- /=.
          case: Ks Eq Ih H1=>//= Kg Ks.
          case Eqg: project =>[Lk|//].
          case EqKs: prj_all =>[Ks''|//].
          rewrite !fsetUs_list => /eqP-[[<- H2]] Ih /andP-[H3 H4].
          by apply: (Ih  Kg)=>//=; [left=>//|apply/eqP]; apply: Eqg.
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
    move: (guarded_open 0 GG C GG')=>/guarded_depth_gt.
    by move=>/(_ _ _ (leq0n 1) (gopen_closed C)).
  Qed.

  (* FIXME: refactor into correct place *)
  Lemma g_guarded_nunroll n iG
    : g_closed iG -> guarded 0 iG -> guarded 0 (n_unroll n iG).
  Proof.
    elim: n iG=>[|n Ih]//;case=>// iG CG /(g_guarded_unroll CG)/Ih-H/=.
    by apply/H/gopen_closed.
  Qed.

  (* FIXME: refactor into correct place *)
  Lemma l_guarded_unroll iG :
    l_closed (l_rec iG) -> lguarded 0 (l_rec iG) ->
    lguarded 0 (l_open 0 (l_rec iG) iG).
  Proof.
    move=> C GG; have GG': (lguarded 1 iG) by move:GG C=>/=; case: iG.
    by move: (lguarded_open 0 GG C GG')=>/lguarded_depth_gt/(_ (lopen_closed C)).
  Qed.

  (* FIXME: refactor into correct place *)
  Lemma l_guarded_nunroll n iL :
    l_closed iL -> lguarded 0 iL -> lguarded 0 (lunroll n iL).
  Proof.
    elim: n iL=>[|n Ih]//;case=>// iG CG /(l_guarded_unroll CG)/Ih-H/=.
    by apply/H/lopen_closed.
  Qed.

  (* FIXME: refactor *)
  Lemma l_closed_unroll n iL :
    l_closed iL -> l_closed (lunroll n iL).
  Proof. by elim: n iL=>[|n Ih]//=; case=>//= iG /lopen_closed/Ih. Qed.

  Lemma v_lty G : (exists v, G = l_var v) \/ (forall v, G != l_var v).
  Proof. by case: G; try (by right); move=>v;left;exists v. Qed.

  Lemma lguarded_lbinds_lt s Lr :
    l_binds s Lr = false ->
    lguarded s Lr ->
    lguarded s.+1 Lr.
  Proof.
    move: {-1}(lrec_depth Lr) (erefl (lrec_depth Lr))=> n E.
    elim: n=>[|n Ih] in s Lr E *.
    - by case: Lr E=>//= v _ /(rwP negPf); rewrite ltn_neqAle eq_sym=>->->.
    - case: Lr E=>//= L [/Ih-E]; apply/E.
  Qed.

  Lemma project_guarded r iG iL :
    project iG r == Some iL ->
    lguarded 0 iL.
  Proof.
    elim/gty_ind1: iG =>[|v|iG Ih/=|p q Ks Ih] in iL *.
    - by move=>/= /eqP-[<-].
    - by move=>/= /eqP-[<-].
    - case Prj: project=>[Lr|//]; move: Prj=>/eqP/Ih-Prj.
      case: ifP; first by move=> _ /eqP-[<-].
      by move=> B /eqP-[<-]/=; apply/lguarded_lbinds_lt.
    - rewrite project_msg.
      case PrjAll: prj_all => [KsL|]//; case: ifP=>// p_n_q.
      case: ifP=>[p_r|p_n_r]; last case: ifP=>[q_r|q_n_r].
      + move=>/eqP-[<-]/=.
        move: PrjAll=>/eqP/prjall_some2-PrjAll.
        apply/forallbP/forall_member=>K M.
        move: (PrjAll _ M)=>[g' [Mks /eqP-Prj]].
        by apply/(Ih _ Mks _ Prj).
      + move=>/eqP-[<-]/=.
        move: PrjAll=>/eqP/prjall_some2-PrjAll.
        apply/forallbP/forall_member=>K M.
        move: (PrjAll _ M)=>[g' [Mks /eqP-Prj]].
        by apply/(Ih _ Mks _ Prj).
      + move=>/eqP-Mrg; move: (prjall_merge_cons PrjAll Mrg)=>[K M].
        move: PrjAll Mrg=>/eqP-PrjAll /eqP-Mrg.
        move: (prjall_merge PrjAll Mrg M)=> H.
        by apply/(Ih _ M).
  Qed.

  Lemma lunroll_end cL :
    LUnroll l_end cL -> cL = rl_end.
  Proof. by move=> /lu_unfold-LU; case Eq: _ _ / LU. Qed.

  Lemma rec_gty G :
    (exists G', G = g_rec G') \/ (forall G', G != g_rec G').
  Proof. by case:G; try (by right); move=> GT; left; exists GT. Qed.

  Lemma matchGrec A G (f : g_ty -> A) g :
    (forall G', G != g_rec G') ->
    match G with
    | g_rec G' => f G'
    | _ => g
    end = g.
  Proof. by case: G=>// GT /(_ GT)/eqP. Qed.

  Lemma rd_zero G :
    (forall G' : g_ty, G != g_rec G') ->
    rec_depth G = 0.
  Proof. by case: G=>// GT /(_ GT)/eqP. Qed.

  Lemma open_notvar n L L' :
    (forall v : nat, L != l_var v) ->
    (forall v : nat, l_open n L' L != l_var v).
  Proof. by case: L=>//v /(_ v)/eqP. Qed.

  Lemma project_var_parts G v r :
    project G r == Some (l_var v) -> r \notin participants G.
  Proof. by apply/project_var_notin/orP/or_intror/eq_refl. Qed.

  Lemma notin_nunroll r n G :
    r \notin participants G ->
    r \notin participants (n_unroll n G).
  Proof.
    elim: n G=>//= n Ih G H.
    by case: G H=>//= GT; rewrite /unroll=>/notin_part_g_open/Ih.
  Qed.

  Fixpoint l_isend L {struct L}:=
    match L with
    | l_rec L => l_isend L
    | l_end => true
    | _ => false
    end.

  Lemma prj_open_binds L1 L2 G r :
    project G r = Some L1 ->
    l_binds 0 L1 ->
    project (g_open 0 (g_rec G) G) r = Some L2 ->
    l_isend L2.
  Proof.
    move=>P1 B1; have []: project G r = Some L1 /\ l_binds 0 L1 by split.
    move: {-2}G  {1 2}L1 =>G' L1'.
    elim/gty_ind1: G' 0 =>[|v|G' Ih|p q Ks' Ih] n // in L1' L2 *.
    - by move=>[<-].
    - by move=>[<-]/=->/=; rewrite P1 B1=> [[<-]].
    - move=>/=; case P: project=>[L''|//].
      case: ifP=>//; first by move=> _ [<-].
      move=> B [<-] {L1'}/= B'.
      case P': project=>[L1'|//].
      case: ifP=> BL1'//; first by move=> [<-].
      by move=>[<-]/=; move: B' P'; apply/Ih.
    - rewrite /g_open !project_msg -/g_open.
      case P: prj_all=>[Ks|//]; case: ifP=>//Npq.
      do ! case: ifP=>[_ [<-]//|_].
      move=>MRG; move: (prjall_merge_cons P MRG) =>[K M].
      move: P MRG=>/eqP-P /eqP-MRG.
      move: (prjall_merge P MRG M)=>/eqP-{P MRG} P B.
      case P': prj_all=>[Ks2|//] /eqP-MRG; move: P'=>/eqP-P'.
      move: (prjall_merge P' MRG)=>{P' MRG} /member_map/(_ _ M)/=/eqP-P'.
      by apply/(Ih _ M n L1' L2).
  Qed.

  Lemma isend_open n L' L :
    l_isend L -> l_open n L' L = L.
  Proof.
    elim/lty_ind2: L=>[|v|L Ih|a p KS Ih]//= in n *; move=> END.
    by rewrite Ih.
  Qed.

  Lemma keep_unrolling L :
    l_isend L -> exists m, l_end = lunroll m L.
  Proof.
    elim/lty_ind2: L=>[||L Ih|]//; [move=>_| move=>/=END; move:(Ih END)=>[n U]].
    - by exists 0.
    - by exists n.+1=>/=; rewrite (isend_open 0 _ END).
  Qed.


 Lemma l_closed_no_binds_aux m n L: m <= n -> l_fidx m L == fset0
    -> l_binds n L = false.
  Proof.
  elim: L m n; rewrite //=.
  + move=> v m n le; case: ifP; 
      [by rewrite -cardfs_eq0 cardfs1 //= 
      | by move=> lefalse; elim; apply: ltn_eqF; 
      apply: (leq_trans _ le); move: (negbT lefalse); rewrite-ltnNge //=].
  + by move=> L IH m n le; apply: IH; rewrite //=.
  Qed.

  Lemma l_closed_no_binds n L: l_closed L -> l_binds n L = false.
  Proof. by apply: l_closed_no_binds_aux. Qed.

  Lemma l_binds_open m n L L1: n != m -> l_closed L1 
    -> l_binds m (l_open n L1 L) = l_binds m L.
  Proof.
  elim: L m n L1.
  + by move=> m n L1 neq closed; rewrite /l_binds //=.
  + move=> v m n L1 neq closed. 
    rewrite /l_binds //=; case: ifP => //=; rewrite <-(rwP eqP); move=>->.
    move: (@l_closed_no_binds m _ closed); rewrite /l_binds; move =>->.
    by move: (negbTE neq).
  + by move=> L IH m n L1 neq closed; rewrite //=; apply: IH.
  + by [].
  Qed.

  (*FIXME: maybe the 2 folowing lemmas are useless,
      anyway they should probably be moved elsewhere*)

  Lemma g_open_msg_rw d G2 FROM TO CONT:
    g_open d G2 (g_msg FROM TO CONT)
    = g_msg FROM TO [seq (K.lbl, (K.mty, g_open d G2 K.cnt)) | K <- CONT].
  Proof. by []. Qed.

  Lemma l_open_msg_rw d L2 a r Ks:
   l_open d L2 (l_msg a r Ks)
   = l_msg a r [seq (K.lbl, (K.mty, l_open d L2 K.cnt)) | K <- Ks].
  Proof. by []. Qed.



  Lemma project_g_open_comm G1 G2 r L1 L2 k: 
    l_closed L1 -> g_closed G1 ->
(*firts hp is not necessary: g_closed + project is sufficient*)
    project G1 r = Some L1 -> project G2 r = Some L2 -> 
    project (g_open k G1 G2) r = Some (l_open k L1 L2).
  Proof.
  elim/gty_ind1: G2 G1 k L1 L2.
  + by move=> G1 k L1 L2 lclo gclo eq1 => //=; move=> [eq2]; rewrite -eq2 //=.
  + by move=> VAR G1 k L1 L2 lclo gclo eq1 => //=; move=> [eq2]; rewrite -eq2 //=; case: ifP.
  + move=> GT IH G1 k L1 L2 lclo gclo eq1 => //=; case Prj: project=>[LT| //=].
    * case: ifP; move=> lbi [eq2]; rewrite //=.
      move: (IH _ (k.+1) L1 LT lclo gclo eq1 Prj) =>->; rewrite -eq2 //=.
      move: (@l_binds_open 0 (k.+1) LT L1) =>-> //=.
      by move: lbi; case: ifP => //=.
    * move: (IH G1 (k.+1) L1 LT lclo gclo eq1 Prj) =>->; move: eq2=><-/=.
      move: (@l_binds_open 0 (k.+1) LT L1) =>-> //=.
      by move: lbi; case: ifP => //=.
  + move=> FROM TO CONT IH G1 k L1 L2 lclo gclo eq1 eq2.
    move: eq2. rewrite g_open_msg_rw project_msg.
    case Pra: prj_all=>[K| //=]; case: ifP; [by rewrite //= | ].
    move=> partdiff; case: ifP; move=> FROMr.
    * move: FROMr partdiff; rewrite <-(rwP eqP) =>->; move=> rTO [lmsgL2].
      rewrite project_msg; rewrite (@prjall_open r k G1 L1 CONT K).
      - move: rTO =>->; move: eq_refl =>-> //=; rewrite <-lmsgL2. 
        by apply f_equal; (*is this really the way to do it?*)
          rewrite l_open_msg_rw.
      - by move=> p mem loc; rewrite <-(rwP eqP); move=> prS; apply IH; rewrite //=.
      - by [].
    * case: ifP; [rewrite <-(rwP eqP) | ]; move=> TOr.
      - rewrite TOr; move=> [lmsgL2]; rewrite project_msg; rewrite (@prjall_open r k G1 L1 CONT K).
        + move: FROMr =>->; move: eq_refl =>-> //=; rewrite <-lmsgL2.
          by apply f_equal; rewrite l_open_msg_rw.
        + by move=> p mem loc; rewrite <-(rwP eqP); move=> prS; apply IH; rewrite //=.  
        + by [].
      - rewrite (rwP eqP); move=> mer; rewrite project_msg; rewrite (@prjall_open r k G1 L1 CONT K).
        + move: partdiff =>->; move: FROMr =>->; move: TOr =>-> //=. 
          by rewrite <-map_comp; rewrite (rwP eqP); apply mergeall_fun. 
        + by move=> p mem loc; rewrite <-(rwP eqP); move=> prS; apply IH; rewrite //=.  
        + by [].
  Qed.

(*  Lemma project_rec_rw G r L: project G r = Some L ->
    project (g_rec G) r = Some (l_rec L).
  Proof.
  rewrite //=; case Prj: project=>[LT| //=].
  move=>eq; move: eq Prj =>[->]; rewrite (rwP eqP); move=> eq.
  move: (project_guarded eq).
*)

  Lemma project_open L G r
        (* (NV : forall v : nat, L != l_var v) *)
        (* (FV : g_fidx 1 G == fset0) *)
        (*(Prj : project G r = Some L)*)
    : l_binds 0 L == false -> g_closed (g_rec G) ->
  project G r = Some L -> project (unroll G) r = Some (l_open 0 (l_rec L) L).
  Proof.
  move=> nlb cl prS.
  have: project (g_rec G) r = Some (l_rec L).
    move: prS; rewrite //=; case Prj: project=>[LT| //=].
    by move=> eq; move: eq Prj nlb=>[<-] Prj; case: ifP=>//=.
  move=> prrecS; apply project_g_open_comm; rewrite //=.
  move: prrecS cl; rewrite /g_closed/l_closed (rwP eqP).
  by move=> pprecs cl; apply (@gclosed_lclosed 0 (g_rec G) r).
  Qed.

(*I need another lemma for the case l_binds 0 L *)

  (* WARNING: depends on project_open *)
  Lemma project_unroll_isend n r G L :
    g_closed G ->
    project G r = Some L ->
    l_isend L ->
    exists L', project (n_unroll n G) r = Some L' /\ l_isend L'.
  Proof.
    elim: n=>[|n Ih]//= in G L *.
    - by move=> closed -> H; exists L.
    - case: G=>[|v|G|p q Ks] closed.
      + by move=> _ _; exists l_end.
      + by move=>[<-].
      + move=>/=.
        case P:project=>[L'|//].
(*
        move: (project_open closed P) => P1.
        case:ifP=>[B _ _|].
        * move: closed (prj_open_binds P B P1) => /gopen_closed-closed END.
          by apply/(Ih _ _ _ P1).
        * move=> _ [<-]/= END; apply/(Ih _ _ _ P1); rewrite ?isend_open//.
          by apply: gopen_closed.
      + by move=>-> H; exists L.
  Qed.
*)
Admitted.

  (* WARNING: depends on project_open *)
  Lemma project_unroll m G r L :
    g_closed G ->
    project G r = Some L ->
    (* g_closed G -> *)
    exists n1 n2 L',
    project (n_unroll m G) r = Some L' /\ lunroll n1 L = lunroll n2 L'.
(*  Proof.
    move=> closed Prj; elim: m => [|m Ih]//= in G closed L Prj *; first (by exists 0,0,L).
    move: closed Prj;case:(rec_gty G)=>[[G'->]|/(@matchGrec g_ty)->];last (by exists 0,0,L).
    move=>/=; case Prj: project=>[L'|]//= closed.
    case: ifP=>//.
    + move: (project_open closed Prj) => Prj'.
      move=> B [U]; move: (prj_open_binds Prj B Prj')=>END.
      move: closed => /gopen_closed-closed.
      move: (project_unroll_isend m closed Prj' END)=>[L0 [-> L0_END]].
      move: (keep_unrolling L0_END)=>[m' U_END].
      by exists m', m', L0; split=>//; rewrite -U -U_END; case: m' {U_END}.
    + move=> _ [<-]{L}.
      move: (project_open closed Prj) => Prj'.
      move: closed => /gopen_closed-closed.
      move: (Ih _ closed _ Prj')=>[n1] [n2] [L0] [PRJ] UNR.
      by exists n1.+1,n2,L0.
  Qed.*) Admitted.

  (* FIXME: refactor somewhere else *)
  Lemma EqL_refl CL : EqL CL CL.
  Proof.
    move: CL {-1 3}CL (erefl CL).
    apply/paco2_acc=> r0 _ CIH CL CL'<- {CL'}.
    apply/paco2_fold.
    case: CL=>//a R C; constructor.
    - by move=> Lb Ty; split=>[[CL ->]|[CL ->]]; exists CL.
    - by move=> Lb Ty CG CG'-> [->]; right; apply: CIH.
  Qed.
  Hint Resolve EqL_refl.
  (* FIXME: abstract all g_closed && guarded ... as "wf" to simplify statements
   *)

  Lemma cproj_all (r0 : proj_rel) FROM CONT CC KsL C
        (CIH : forall cG cL iG iL,
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
    rewrite /R_all=> Lb Ty G G' CC_Lb C_Lb; right.
    elim: GU CC_Lb cG gG KsL C C_Lb LU PRJ =>//.
    move=>/= Lb' Ty' IG CG Ks CCG [UIG UA|//] Ih E_CCG cG gG.
    case Prj: project=>[L|]//; case PAll: prj_all=>[KsL'|]// KsL C C_Lb LU E.
    move: Prj E LU=> /eqP-Prj [<-]{KsL} LU.
    case Eq: _ _/ LU C_Lb Ih  => [|Lb0 Ty0 L0 cL0 KsL CL [UL|//] UAL]// {C}.
    move: Eq UL UAL =>[<-<-<-<-] {Lb0 Ty0 L0 KsL} UL UAL.
    rewrite /extend; case: ifP.
    + move=>E; move: E E_CCG cG gG=>/eqP->{Lb'} E_CCG cG gG [ETy].
      move: E_CCG; rewrite /extend eq_refl=>[[_ ECG]].
      move: ETy cG gG=>->{Ty'} cG gG <-{G'} _.
      move: (cG _ (or_introl erefl))=>/= /CIH-{CIH}CIH.
      move: (gG _ (or_introl erefl))=>/= /CIH/(_ Prj UIG UL).
      by move: ECG=>->.
    + move=>N CL_Lb Ih; move: E_CCG; rewrite /extend N=>/Ih-{Ih}Ih.
      move: cG gG=>/(_ _ (or_intror _))-cG /(_ _ (or_intror _))-gG.
      by move: (Ih cG gG) CL_Lb =>{Ih}Ih /Ih/(_ UAL PAll).
  Qed.

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
        (CIH : forall cG cL iG iL,
            g_closed iG ->
            guarded 0 iG ->
            project iG r == Some iL ->
            GUnroll iG cG ->
            LUnroll iL cL ->
            r0 cG cL)
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
      + move=>[EL]; move: EL LU=><- {L} /lu_unfold-LU.
        case EL: _ _/LU=>[||a p Ks C LU]//; move: EL LU=>[<-<-<-] LU {a p Ks}.
        move: F_r CIH E=>/eqP<-{r} CIH E; apply/prj_send1; first by apply/negPf.
        apply/(cproj_all CIH cG gG GU LU)=>//.
      + case:ifP=>[T_r | T_ne_r].
        * move=>[EL]; move: EL LU=><- {L} /lu_unfold-LU {F_ne_r}.
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
    move=> iG iL cG cL CG GG Prj GU LU.
    move: (conj CG (conj GG (conj Prj (conj GU LU)))) => {CG GG Prj GU LU}.
    move => /(ex_intro (fun iL=> _) iL) {iL}.
    move => /(ex_intro (fun iG=> _) iG) {iG}.
    move: cG cL; apply/paco2_acc=> r0 _ CIH.

    move: CIH=>/(_ _ _ (ex_intro _ _ _)).
    move =>/(_ _ _ _ (ex_intro _ _ _)).
    move =>/(_ _ _ _ _ (conj _ _)).
    move =>/(_ _ _ _ _ _ (conj _ _)).
    move =>/(_ _ _ _ _ _ _ (conj _ _)).
    move =>/(_ _ _ _ _ _ _ _ (conj _ _))-CIH.
    move=> cG cL [iG] [cG'] [ciG] [giG] [iGiL] [GU LU].

    move: iGiL  => /eqP-iGiL.
    move: (project_unroll (rec_depth iG) ciG iGiL) => [U1] [U2] [L] [proj] U12.
    move: LU =>/(LUnroll_ind U1); move: U12=>->; rewrite -LUnroll_ind=>UL.
    move : GU (unroll_guarded ciG giG)=>/(GUnroll_ind (rec_depth iG))=>GU nrG.
    move: (g_guarded_nunroll (rec_depth iG) ciG giG)=>guiG.
    move: (g_closed_unroll (rec_depth iG) ciG)=>cuiG {ciG giG iGiL}.
    by apply/(project_nonrec CIH cuiG guiG nrG proj).
  Qed.
End CProject.

Print Assumptions ic_proj.
