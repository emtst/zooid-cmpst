From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco1 paco2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.AtomSets.
Require Import MPST.Forall.
Require Import MPST.Global.
Require Import MPST.Local.
Require Import MPST.Session.
Require Import MPST.Actions.
Require Import MPST.Atom.

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
    elim: G 0 =>[|v|G Ih|q r Ks Ih] n//= in Lp BLp Ep *.
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
    elim: G => [|v'|G Ih|q r Ks Ih]// in L v *.
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
    elim: G =>[//|v//=|G Ih//=|r s Ks Ih] in Lq Sq *.
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
    elim: G => [|n|G Ih|f t Ks Ih]// in v v' *.
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
  (*   elim: G=>[|v|G Ih|q r Ks Ih] in Lp NIN Ep *; move: Ep=>[]. *)
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
  (*   elim: G=>[|v|G Ih|q r Ks Ih] in L *. *)
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
    elim: G=>[|v|G Ih|r s Ks Ih] in Lp Lq n m *.
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

  Definition Merge (F : lbl /-> mty * rl_ty) (L : rl_ty) : Prop :=
    forall Lb Ty L', F Lb = Some (Ty, L') -> EqL L' L.

  Inductive WF_ (r : rg_ty -> Prop) : rg_ty -> Prop :=
  | WF_end : WF_ r rg_end
  | WF_msg F T C :
      F != T ->
      P_all r C ->
      (exists l Ty G, C l = Some (Ty, G)) ->
      WF_ r (rg_msg F T C).
  Definition WF := paco1 WF_ bot1.

  Lemma WF_mon : monotone1 WF_.
  Proof.
    move=> G r r' [].
    - by move=> _; apply/WF_end.
    - by move=> F T C FT ALL NE H; apply/WF_msg=>// l Ty {}G Cl; apply/H/ALL/Cl.
  Qed.

  Definition proj_rel := rg_ty -> rl_ty -> Prop.
  Inductive Proj_ (p : role) (r : proj_rel) : proj_rel :=
  | prj_end G : ~ part_of p G -> WF G -> Proj_ p r G rl_end
  | prj_send q KsG KsL :
      p != q ->
      same_dom KsG KsL ->
      R_all r KsG KsL ->
      Proj_ p r (rg_msg p q KsG) (rl_msg l_send q KsL)
  | prj_recv q KsG KsL :
      p != q ->
      same_dom KsG KsL ->
      R_all r KsG KsL ->
      Proj_ p r (rg_msg q p KsG) (rl_msg l_recv q KsL)
  | prj_mrg q s KsG KsL L :
      q != s ->
      p != q ->
      p != s ->
      (exists l Ty G, KsG l = Some (Ty, G)) ->
      P_all (part_of_all p) KsG ->
      same_dom KsG KsL ->
      R_all r KsG KsL ->
      Merge KsL L ->
      Proj_ p r (rg_msg q s KsG) L
  .
  Hint Constructors Proj_.
  Derive Inversion Proj__inv  with (forall p r G L, Proj_ p r G L) Sort Prop.

  Lemma Proj_monotone p : monotone2 (Proj_ p).
  Proof.
  rewrite /monotone2; move=> x0 x1 r r' it LE; move: it; case=>//.
  + by move=>G part; constructor.
  + move=> q KsG KsL neq samed HP; constructor =>//; move: HP; rewrite /R_all.
    move=> HP l Ty G L KsG_l KsL_l; apply: LE; by apply: (@HP l Ty G L KsG_l KsL_l).
  + move=> q KsG KsL neq samed rall; constructor =>//; move: rall; rewrite /R_all.
    move=> rall l t G L KsG_l KsL_l; apply: LE. by apply: (rall _ _ _ _ KsG_l KsL_l).
  + move=> q s KsG KsL L0 neq_qs neq_pq neq_ps NE parts samed rall merg.
    apply (@prj_mrg _ _ _ _ KsG KsL _) =>//; move: rall; rewrite /R_all.
    move=> rall l t G L KsG_l KsL_l; apply: LE; by apply: (rall _ _ _ _ KsG_l KsL_l).
  Qed.
  Hint Resolve Proj_monotone.
  Definition Project p CG CL := paco2 (Proj_ p) bot2 CG CL.

  Lemma Project_inv (p : role) (G : rg_ty) (L : rl_ty)
        (P : (let (sort, _) := role in sort) -> rg_ty -> rl_ty -> Prop) :
    (forall G0, G0 = G -> rl_end = L -> ~ part_of p G0 -> WF G0 -> P p G0 rl_end) ->
    (forall q CG CL,
       rg_msg p q CG = G -> rl_msg l_send q CL = L ->
       p != q -> same_dom CG CL -> R_all (Project p) CG CL ->
       P p (rg_msg p q CG) (rl_msg l_send q CL)) ->
    (forall q CG CL,
       rg_msg q p CG = G -> rl_msg l_recv q CL = L ->
       p != q -> same_dom CG CL -> R_all (Project p) CG CL ->
       P p (rg_msg q p CG) (rl_msg l_recv q CL)) ->
    (forall (q s : role) CG CL L0,
        q != s -> p != q -> p != s ->
        rg_msg q s CG = G -> L0 = L ->
        (exists l Ty G, CG l = Some (Ty, G)) ->
        P_all (part_of_all p) CG -> same_dom CG CL -> R_all (Project p) CG CL ->
        Merge CL L -> P p (rg_msg q s CG) L) ->
    Project p G L -> P p G L.
  Proof.
    move=> Hend Hsnd Hrcv Hmrg /(paco2_unfold (Proj_monotone (p:=p))).
    elim/Proj__inv =>/(paco2_fold _ _ _ _); rewrite -/(Project p G L) => PRJ.
    + by move=> G0 PART WF EQ1 EQ2; apply/Hend.
    + move=> q CG CL pq DOM ALL EQ1 EQ2; apply/Hsnd=>//.
      by move=>l Ty G0 G1 CGl CLl; move: (ALL l Ty G0 G1 CGl CLl)=>[|//].
    + move=> q CG CL pq DOM ALL EQ1 EQ2; apply/Hrcv=>//.
      by move=>l Ty G0 G1 CGl CLl; move: (ALL l Ty G0 G1 CGl CLl)=>[|//].
    + move=> q s CG CL L0 qs pq ps NE Part DOM ALL MRG EQ1 EQ2; apply/Hmrg=>//.
      by move=>l Ty G0 G1 CGl CLl; move: (ALL l Ty G0 G1 CGl CLl)=>[|//].
  Qed.

  Lemma dom T T' (C0 : lbl /-> mty * T) (C1 : lbl /-> mty * T')
        (DOM : same_dom C0 C1)
    : forall l Ty G, C0 l = Some (Ty, G) -> exists G', C1 l = Some (Ty, G').
  Proof. by move=> l Ty; move: (DOM l Ty)=>[/(_ (ex_intro _ _ _))-H _]. Qed.

  Lemma dom' T T' (C0 : lbl /-> mty * T) (C1 : lbl /-> mty * T')
        (DOM : same_dom C0 C1)
    : forall l Ty G, C1 l = Some (Ty, G) -> exists G', C0 l = Some (Ty, G').
  Proof. by move=> l Ty; move: (DOM l Ty)=>[_ /(_ (ex_intro _ _ _))-H]. Qed.

  Lemma samed_eql C0 C :
    R_all EqL C0 C ->
    same_dom C0 C ->
    forall l Ty L,
      C l = Some (Ty, L) -> exists L', C0 l = Some (Ty, L') /\ EqL L' L.
  Proof.
    move=> ALL DOM l Ty L Cl; move: (dom' DOM Cl)=>[L' C0l].
    by move: (ALL l Ty L' L C0l Cl)=> EQ; exists L'; split.
  Qed.

  Lemma EqL_Project p G lT lT':
    EqL lT lT' -> Project p G lT -> Project p G lT'.
  Proof.
  move=> eql prj; move: (conj eql prj) => {eql prj}.
  move=> /(ex_intro (fun lT=> _) lT) {lT}.
  move: G lT'; apply /paco2_acc; move=> r0 _ CIH G lT'.
  move: CIH=>/(_ _ _ (ex_intro _ _ (conj _ _)))-CIH.
  elim=> lT; elim; case lT'.
  + move=> eql; move: (EqL_r_end_inv eql); move=>->.
    rewrite /Project; move=> pro; move: paco2_mon; rewrite /monotone2.
    by move=> pamo; apply (pamo _ _ _ _ _ _ _ pro).
  + move=> a q C eql; move: (EqL_r_msg_inv eql).
    elim=> C0; elim=> samed; elim=> rall lTeq; rewrite lTeq.
    move=>PRJ; move: PRJ eql; elim/Project_inv=>//.
    * move=> q0 CG CL _ [<-->->] NE1 DOM ALL EQ_L {G q0}.
      apply/paco2_fold; constructor=>//; first by apply: (same_dom_trans DOM).
      move=>l Ty G G' CGl Cl; move: (samed_eql rall samed Cl)=>[L' [C0l EQ_L']].
      right; apply/CIH; first by apply/EQ_L'.
      by apply/(ALL _ _ _ _ CGl C0l).
    * move=> q0 CG CL _ [<-->->] NE1 DOM ALL EQ_L {G q0}.
      apply/paco2_fold; constructor=>//; first by apply: (same_dom_trans DOM).
      move=>l Ty G G' CGl Cl; move: (samed_eql rall samed Cl)=>[L' [C0l EQ_L']].
      right; apply/CIH; first by apply/EQ_L'.
      by apply/(ALL _ _ _ _ CGl C0l).
    * move=> r s CG CL L0 NE1 NE2 NE3 _ _  NE part DOM ALL MRG.
      move=> _ {G L0 lTeq lT}; apply/paco2_fold/prj_mrg=>//.
      - move=>l Ty G G' CGl Cl; right; apply/CIH; first by apply/EqL_refl.
        by apply/ALL; first by apply/CGl.
      - move=> l Ty L' CLl; move: (MRG l Ty  L' CLl).
        move=>/EqL_trans-H; apply: H; apply/paco2_fold; constructor=>//.
        by move=> l0 Ty0 L0 L1 C0l0 Cl0; left; apply/(rall _ _ _ _ C0l0 Cl0).
  Qed.


  Lemma gclosed_lclosed d G r L :
    g_fidx d G == fset0 ->
    project G r == Some L ->
    l_fidx d L == fset0.
  Proof.
    elim: G =>[|v|G Ih|p q Ks Ih] in d L *.
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
          rewrite !fsetUs_list => /eqP-[<- H2] Ih /andP-[H3 H4].
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


  Lemma project_guarded r iG iL :
    project iG r == Some iL ->
    lguarded 0 iL.
  Proof.
    elim: iG =>[|v|iG Ih/=|p q Ks Ih] in iL *.
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


  Lemma project_var_parts G v r :
    project G r == Some (l_var v) -> r \notin participants G.
  Proof. by apply/project_var_notin/orP/or_intror/eq_refl. Qed.


  Lemma prj_open_binds L1 L2 G r :
    project G r = Some L1 ->
    l_binds 0 L1 ->
    project (g_open 0 (g_rec G) G) r = Some L2 ->
    l_isend L2.
  Proof.
    move=>P1 B1; have []: project G r = Some L1 /\ l_binds 0 L1 by split.
    move: {-2}G  {1 2}L1 =>G' L1'.
    elim: G' 0 =>[|v|G' Ih|p q Ks' Ih] n // in L1' L2 *.
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

(*FIXME: just a coq question from Lorenzo to David and Francisco*)

  Lemma project_g_open_comm G1 G2 r L1 L2 k:
    g_closed G1 ->
    project G1 r = Some L1 -> project G2 r = Some L2 ->
    project (g_open k G1 G2) r = Some (l_open k L1 L2).
  Proof.
  elim: G2 G1 k L1 L2.
  + by move=> G1 k L1 L2 gclo eq1 => //=; move=> [eq2]; rewrite -eq2 //=.
  + by move=> VAR G1 k L1 L2 gclo eq1 => //=; move=> [eq2]; rewrite -eq2 //=; case: ifP.
  + move=> GT IH G1 k L1 L2 gclo eq1 => //=; case Prj: project=>[LT| //=].
    * case: ifP; move=> lbi [eq2]; rewrite //=.
      move: (IH _ (k.+1) L1 LT gclo eq1 Prj) =>->; rewrite -eq2 //=.
      move: (@l_binds_open 0 (k.+1) LT L1) =>-> //=.
      + by move: lbi; case: ifP => //=.
      + by move: eq1; rewrite (rwP eqP); apply gclosed_lclosed.
    * move: (IH G1 (k.+1) L1 LT gclo eq1 Prj) =>->; move: eq2=><-/=.
      move: (@l_binds_open 0 (k.+1) LT L1) =>-> //=.
      + by move: lbi; case: ifP => //=.
      + by move: eq1; rewrite (rwP eqP); apply gclosed_lclosed.
  + move=> FROM TO CONT IH G1 k L1 L2 lclo eq1 eq2.
    move: eq2; rewrite g_open_msg_rw project_msg.
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

  Lemma project_open L G r
    : l_binds 0 L == false -> g_closed (g_rec G) ->
  project G r = Some L -> project (unroll G) r = Some (l_open 0 (l_rec L) L).
  Proof.
  move=> nlb cl prS.
  have: project (g_rec G) r = Some (l_rec L).
    move: prS; rewrite //=; case Prj: project=>[LT| //=].
    by move=> eq; move: eq Prj nlb=>[<-] Prj; case: ifP=>//=.
  move=> prrecS; apply project_g_open_comm; rewrite //=.
  Qed.

  Lemma project_open_end_strong L G1 G r k:
    project G r = Some L -> project G1 r = Some (l_end)->
    project (g_open k G1 G) r = Some (l_open k l_end L).
  Proof.
  elim: G L G1 k.
  + by rewrite //=; move=> L G1 k [eq] pro; rewrite -eq.
  + rewrite //=; move=> v L G1 k [eq] pro; rewrite -eq.
    case: ifP.
     * by rewrite -(rwP eqP) pro; move=>->//=; case: ifP; rewrite eq_refl.
     * by rewrite //=; case: ifP.
  + move=> G Ih L G1 k; rewrite //=; case prG: project=> [LT|] //.
    case: ifP=> //; move=> lbi' [eq] pro'.
    * rewrite (@Ih LT G1 (k.+1) prG pro') -eq.
      by rewrite (@l_binds_open 0 (k.+1) LT l_end) //=; move: lbi'; case: ifP.
    * rewrite (@Ih LT G1 (k.+1) prG pro') -eq.
      by rewrite (@l_binds_open 0 (k.+1) LT l_end) //=; move: lbi'; case: ifP.
  + move=> FROM TO CONT Ih L G1 k prG pro'; move: prG; rewrite g_open_msg_rw project_msg.
    case Pra: prj_all=>[K| //=]; case: ifP; [by rewrite //= | ].
    move=> FROMTO; case: ifP; move=> FROMr.
    * move: FROMr FROMTO; rewrite <-(rwP eqP) =>->; move=> rTO [eq].
      rewrite project_msg; rewrite (@prjall_open r k G1 l_end CONT K).
      - move: rTO =>->; move: eq_refl =>-> //=; rewrite <-eq.
        by apply f_equal; rewrite l_open_msg_rw.
      - by move=> p mem loc; rewrite <-(rwP eqP); move=> prS; apply Ih; rewrite //=.
      - by [].
    * case: ifP; [rewrite <-(rwP eqP) | ]; move=> TOr.
      - rewrite TOr; move=> [eq]; rewrite project_msg; rewrite (@prjall_open r k G1 l_end CONT K).
        + move: FROMr =>->; move: eq_refl =>-> //=; rewrite <-eq.
          by apply f_equal; rewrite l_open_msg_rw.
        + by move=> p mem loc; rewrite <-(rwP eqP); move=> prS; apply Ih; rewrite //=.
        + by [].
      - rewrite (rwP eqP); move=> mer; rewrite project_msg; rewrite (@prjall_open r k G1 l_end CONT K).
        + move: FROMTO =>->; move: FROMr =>->; move: TOr =>-> //=.
          by rewrite <-map_comp; rewrite (rwP eqP); apply mergeall_fun.
        + by move=> p mem loc; rewrite <-(rwP eqP); move=> prS; apply Ih; rewrite //=.
        + by [].
  Qed.


  Lemma project_open_end L G r : l_binds 0 L -> project G r = Some L
    -> project (unroll G) r = Some (l_open 0 l_end L).
  Proof.
  move=> lbi pro; apply project_open_end_strong; move: pro; rewrite //=.
  by case Prj: project=>[LT| //=]; move=> eq; move: eq Prj lbi=>[<-] Prj; case: ifP.
  Qed.

  Lemma lbinds_open_end_strong L k: l_binds k L -> l_isend (l_open k l_end L).
  Proof.
  elim: L k=> //.
  + by move=> v k; rewrite /l_binds -(rwP eqP)=>->/=; case: ifP; rewrite eq_refl.
  + by move=> L ih k //=; apply ih.
  Qed.


  Lemma lbinds_open_end L: l_binds 0 L -> l_isend (l_open 0 l_end L).
  Proof.
  by apply lbinds_open_end_strong.
  Qed.

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
      case P:project=>[L'|//]; case: ifP.
      * move=> lbi [eq] isend. apply (@Ih _ (l_open 0 l_end L')).
        - by rewrite /unroll; apply gopen_closed.
        - by apply project_open_end.
        - by apply lbinds_open_end.
      * rewrite (rwP eqP); move=> lbi.
        move: (project_open lbi closed P) => P1 [eq] isend.
        apply (Ih _ (l_open 0 (l_rec L') L')); rewrite //=.
        - by rewrite /unroll; apply gopen_closed.
        - move: isend; rewrite -eq => //=; move=> isend; rewrite isend_open //=.
    + by move=>-> H; exists L.
  Qed.

  Lemma project_unroll m G r L :
    g_closed G ->
    project G r = Some L ->
    (* g_closed G -> *)
    exists n1 n2 L',
    project (n_unroll m G) r = Some L' /\ lunroll n1 L = lunroll n2 L'.
    Proof.
    move=> closed Prj; elim: m => [|m Ih]//= in G closed L Prj *; first (by exists 0,0,L).
    move: closed Prj;case:(rec_gty G)=>[[G'->]|/(@matchGrec g_ty)->];last (by exists 0,0,L).
    move=>/=; case Prj: project=>[L'|]//= closed.
    case: ifP=>//.
    + move=> lbi; move: (project_open_end lbi Prj) => Prj'.
      move=> [U]; move: (prj_open_binds Prj lbi Prj')=>END.
      move: closed => /gopen_closed-closed.
      move: (project_unroll_isend m closed Prj' END)=>[L0 [-> L0_END]].
      move: (keep_unrolling L0_END)=>[m' U_END].
      by exists m', m', L0; split=>//; rewrite -U -U_END; case: m' {U_END}.
    + rewrite (rwP eqP).
      move=> nlbi [<-]{L}.
      move: (project_open nlbi closed Prj) => Prj'.
      move: closed => /gopen_closed-closed.
      move: (Ih _ closed _ Prj')=>[n1] [n2] [L0] [PRJ] UNR.
      by exists n1.+1,n2,L0.
  Qed.

  (* FIXME: abstract all g_closed && guarded ... as "wf" to simplify statements*)

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
    - move=>/= Lb' Ty' IG CG [UIG UA|//] cG gG Ks cGL c UAL.
      case PRJ: project=>[L|]// [][KsL].
      move: KsL UAL=><-.
      elim/lunr_all_inv =>//  _ Lb0 Ty0 L0 cL0 KsL0 CCL0 [UL0|//] _.
      move=>E; move: E cL0 UL0 =>[->->->] _ cL UL EX {Lb0 Ty0 L0 KsL0}.
      move: UA; rewrite /extend; case: ifP=>//E [ETy' <-].
      move: c; rewrite -EX /extend E =>[][_]<-.
      move: (cG ((Lb', (Ty', IG))) (or_introl erefl))=>/= cIG.
      move: (gG ((Lb', (Ty', IG))) (or_introl erefl))=>/= gIG.
      by move: PRJ CIH=>/eqP-PRJ /(_ CG cL IG L cIG gIG PRJ UIG UL).
    - move=>/= Lb' Ty' IG CG Ks CCG [UIG UA|//] Ih E_CCG cG gG.
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



  Lemma cproj_samedom p gCONT lCONT gC lC
        (GU : @unroll_all (upaco2 g_unroll bot2) gCONT gC)
        (LU : l_unroll_all (upaco2 l_unroll bot2) lCONT lC)
        (PRJ : prj_all gCONT p = Some lCONT)
    : same_dom gC lC.
  Proof.
  elim: GU lCONT lC LU PRJ =>//=.
  + move=> l Ty' iG cG [UG|//] lCONT lC UAL.
    case: (project iG p) =>//=; move=> lT.
    move=> hp; move: hp UAL=>[<-].
    elim/lunr_all_inv => // _ l0 Ty0 L0 CL0 KL0 KCL0 [_|//] UL.
    move=>E; move: E UL=>[->-> _ ->] UL _.
    elim/lunr_all_inv: UL => // _ _ _.
    move=> l' Ty''; rewrite /extend/empty/=.
    by split=>[][IG]; case: ifP=>// _ [<-] _; [exists CL0 | exists cG].
  + move=> l Ty' iG cG gCONT0 gC0 gun unrall IHP lCONT lC lunrall.
    case: (project iG p) =>//=; move=> lT.
    move=> hp; move: hp IHP; case: (prj_all gCONT0 p) =>//=.
    move=> lCONT0 [lCONTeq] IH; move: lCONTeq.
    have IH_good: forall lC,
      l_unroll_all (upaco2 l_unroll bot2) lCONT0 lC -> same_dom gC0 lC.
      by move=> lC0 hp; apply: (IH lCONT0) =>//=.
    move: IH; move=> _ . (*I have removed a bad hp*)
    move: unrall IH_good. case: lunrall lCONT0 gC0 =>//=.
    move => l0 t iT cT ilC clC upa lunrall lCONT0 gC0 unrall IH [eq].
    move=> eqTy eqloc eqlcont; rewrite eq eqTy; apply: same_dom_extend.
    by apply IH; rewrite eqlcont.
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

  Fixpoint l_isvar L :=
    match L with
    | l_var v => true
    | l_rec L => l_isvar L
    | _ => false
    end.

  (* Depth that guarantees that we find all occurrences of p *)
  Fixpoint depth_part n p G :=
    match n with
    | 0 => false
    | m.+1 =>
      match G with
      | g_msg q r Ks => if (p == q) || (p == r) then true
                        else all (depth_part m p) [seq K.cnt | K <- Ks ]
      | g_rec G => depth_part m p G
      | _ => false
      end
    end.

  Lemma depth_next n m p G :
    n <= m ->
    depth_part n p G ->
    depth_part m p G.
  Proof.
    elim: G=>[|v|G Ih|F T C Ih]//= in n m *; case: n=>//; case m=>//.
    - by move=>n {}m/= LE; apply/Ih.
    - move=>n {}m/= LE; case: ifP=>//pFT /forallbP/forall_member/member_map-H.
      apply/forallbP/forall_member/member_map=>x M.
      by apply/(Ih _ M _ _ _ (H _ M)).
  Qed.

  Lemma lbinds_isvar n L : l_binds n L -> l_isvar L.
  Proof. by elim: L n =>//= L Ih n /Ih. Qed.

  Lemma project_depth' p G L :
    project G p == Some L ->
    ~~ (l_isend L || l_isvar L) <->
    exists n, depth_part n p G.
  Proof.
    elim: G =>[|v|G Ih|F T C Ih]/= in L *; try move=>/eqP[<-]/=.
    - by split=>// [[[]//]].
    - by split=>// [[[]//]].
    - case PRJ: project=>[L'|]//; move: PRJ=>/eqP-PRJ.
      case: ifP=> B /eqP-[<-]/=.
      + split=>// [][[|n]]//= H; move: (ex_intro (fun n=>_) n H) => {n H}.
        by move=>/(Ih _ PRJ); rewrite negb_or (lbinds_isvar B) andbC.
      + move: (Ih _ PRJ)=>{}Ih; rewrite Ih=> {Ih B PRJ}.
        split=>[][[|n]]//; last by exists n.
        by exists n.+2.
    - rewrite -/prj_all.
      case PRJ: prj_all=>[Ks|]//; case: ifP=>// FT.
      case: ifP=>[|].
      + by move=>/eqP<-/eqP-[<-]; split=>// _; exists 1; rewrite /=eq_refl.
      case: ifP=>[|].
      + by move=>/eqP<- _/eqP-[<-];split=>//_; exists 1; rewrite /=eq_refl orbC.
      + rewrite eq_sym=> pT; rewrite eq_sym =>pF MRG; split.
        * move=> VAR; move: Ih=>/(_ _ _ L); rewrite VAR=>Ih.
          move: PRJ=>/eqP-PRJ; move: (prjall_merge PRJ MRG)=>{}PRJ.
          have {}Ih: forall K,
              member K C -> exists n : nat, depth_part n p K.cnt
                by move=> K M; move: PRJ Ih=>/(_ _ M)-PRJ /(_ _ M PRJ)-<-.
          move => {PRJ VAR MRG Ks L}.
          suff: exists n, forall K, member K C -> depth_part n p K.cnt
                by move=>[n H]; exists n.+1=>/=; rewrite pF pT/=;
                     apply/forallbP/forall_member/member_map.
          move=> {FT pF pT F T}; elim: C=>[|K C IhC] in Ih *; first by (exists 0).
          move: (Ih K (or_introl erefl))=>[n DK].
          move: Ih=>/(_ _ (or_intror _))=>/IhC-[m] H.
          exists (maxn n m)=> K' [->|/H-{}DK]; apply/(depth_next _ DK).
          by apply/leq_maxl.
          by apply/leq_maxr.
        * move=> [[|n]//= ]; rewrite pF pT/=.
          move: MRG=>/eqP-MRG; move: (prjall_merge_cons PRJ MRG)=>[K M].
          move=>/forallbP/forall_member/member_map/( _ _ M)-DP.
          move: (ex_intro (fun n=>_) n DP); rewrite -(Ih K M L)//.
          by move: PRJ MRG=>/eqP-PRJ /eqP-MRG; move: (prjall_merge PRJ MRG M).
  Qed.

  Lemma guarded_closed_notvar L :
    l_closed L ->
    lguarded 0 L ->
    l_isvar L = false.
  Proof.
    rewrite /l_closed; elim: L 0=>//=.
    - by move=> v n; case: ifP=>//; rewrite -cardfs_eq0 cardfs1.
    - by move=>L Ih n; apply/Ih.
  Qed.

  Lemma project_depth p G L :
    g_closed G ->
    project G p == Some L ->
    ~~ l_isend L <-> exists n, depth_part n p G.
  Proof.
    move=> cG PRJ; split.
    + move=>pG; move: (gclosed_lclosed cG PRJ) (project_guarded PRJ)=>cL gL.
      move: (guarded_closed_notvar cL gL)=>/(rwP negPf)/(conj pG)/andP.
      by rewrite -negb_or (project_depth' PRJ).
    + by rewrite -(project_depth' PRJ) negb_or=>/andP-[].
  Qed.

  Lemma depthpart_open v n p G G' :
    depth_part n p G ->
    depth_part n p (g_open v G' G).
  Proof.
    elim: G=>[|v'|G Ih|F T C Ih]//= in n v *; case: n=>// n/=.
    - by apply/Ih.
    - case:ifP=>// _ /forallbP/forall_member/member_map-DP.
      apply/forallbP/forall_member/member_map/member_map=>/= K M.
      by apply/(Ih _ M)/DP.
  Qed.

  Lemma lbinds_depth p G L n k :
    project G p == Some L -> l_binds k L -> depth_part n p G = false.
  Proof.
    move=>/project_depth'=>[][_ /(_ (ex_intro _ n _))-H B]; move: H.
    rewrite negb_or andbC (lbinds_isvar B)=>/=; case: depth_part=>//.
    by move=>/(_ is_true_true).
  Qed.

  Lemma unroll_all_exists_i CONT CC l Ty CG :
    @unroll_all (upaco2 g_unroll bot2) CONT CC ->
    CC l = Some (Ty, CG) ->
    exists K, member K CONT /\ K.1 = l /\ GUnroll K.2.2 CG.
  Proof.
    elim: CONT CC.
    - move=> CC; by case E: _ _ / =>//.
    - move=> K Ks Ih CC.
      case E: _ _ / =>[l' Ty' iG cG [|//]|l' Ty' iG cG iK cK GU UA]//; rewrite /extend;
         first (by move=> H1; move: H1 E; case: ifP=>///eqP-> [-><-] _;
                   exists (l, (Ty, iG)); split=>//=; first (by left); split).
      case: ifP.
      + move=>/eqP-EQ_l [_ <-].
        exists (l', (Ty', iG)) =>/=; split; first by left.
        by split=>//; move: GU=>[|//].
      + move=> ll' cKl; move: E UA=>[_ <-] /Ih/(_ cKl)-[K' [M'] [E] GU'].
        exists K'=>/=; split; first by right.
        by split.
  Qed.

  Lemma partof_all_unroll G CG p L n :
    g_closed G ->
    GUnroll G CG -> project G p == Some L ->
    depth_part n p G -> part_of_all p CG.
  Proof.
    elim: n G CG L=>// n Ih [||G|F T C] //= CG L cG; rewrite -/prj_all.
    - case PRJ: project=>[L0|]//; move: PRJ=>/eqP-PRJ.
      case: ifP; first by move=>/(lbinds_depth _ PRJ)->.
      move=> NB /gunroll_unfold; elim/gunr_inv=>// _ IG CG0 GU [EQ1] EQ2 _ DP.
      move: EQ1 EQ2 GU DP=>//-> _ []//GU /(depthpart_open 0 (g_rec G))-DP.
      move: NB PRJ=>/eqP-NB /eqP-PRJ; move: (project_open NB cG PRJ)=>{}/eqP-P.
      by move: cG=>/gopen_closed/Ih/(_ GU P DP).
    - move=>/gunroll_unfold; elim/gunr_inv=>// _ F' T' C' CC UA E1 _ {CG}.
      move: E1 UA=>[->->->] UA {F' T' C'}.
      case PRJ: prj_all=>[Ks|]//; case: ifP=>// FT.
      case: ifP=>[/eqP<- _|pF]; first by constructor.
      case: ifP=>[/eqP<- _|pT]; first by constructor.
      move=>MRG; rewrite eq_sym pF eq_sym pT/= => DP.
      apply: pall_cont=>l Ty CG CCl.
      move: (unroll_all_exists_i UA CCl) PRJ=>[K] [M] [_] GU /eqP-PRJ.
      move: (prjall_merge PRJ MRG)=>P.
      move: (P _ M)=>PRJ_K; apply: (Ih _ _ _ _ GU PRJ_K).
      * by move: cG; rewrite /g_closed/= fsetUs_fset0=>/member_map/(_ _ M).
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
      by move=> F' T' C' CG' _ _ [->] _ _ _; rewrite in_cons eq_refl.
    - apply: r_in_unroll_rec_depth; move: GU=>/(GUnroll_ind (rec_depth G)).
      move: (n_unroll (rec_depth G) G) (unroll_guarded cG gG)=>{cG gG}G NR GU.
      move: GU NR=>/gunroll_unfold; elim/gunr_inv =>// _;
        first by move=> IG _ _ _ _ /(_ IG); rewrite eq_refl.
      by move=> F' T' C' CG' _ _ [] _ <- _ _; rewrite in_cons orbC in_cons eq_refl.
    - apply: r_in_unroll_rec_depth; move: GU=>/(GUnroll_ind (rec_depth G)).
      move: (g_guarded_nunroll (rec_depth G) cG gG) (unroll_guarded cG gG).
      move: (n_unroll (rec_depth G) G) (g_closed_unroll (rec_depth G) cG).
      move=>{cG gG}G cG gG NR GU.
      move: GU NR cG gG =>/gunroll_unfold; elim/gunr_inv =>// _;
        first by move=> IG _ _ _ _ /(_ IG); rewrite eq_refl.
      move=> F' T' C' CG' UA E1 E2 _ .
      rewrite /g_closed/==>/fsetUs_fset0/member_map-cG.
      move=>/forallbP/forall_member=>gG.
      move: E1 E2 cG gG UA=>_ [->->->] cG gG UA {G F' T' CG'}.
      suff: p \in flatten [seq participants K.cnt | K <- C']
        by rewrite !in_cons=>->; rewrite orbC orbT.
      move: (unroll_all_exists_i UA Cl)=>[K][M][_]GU.
      apply/flatten_mapP; exists K; first by apply/memberP.
      by apply/(Ih _ (cG _ M) (gG _ M) GU).
  Qed.

  Lemma project_parts' p G L :
    project G p == Some L ->
    p \notin participants G ->
    l_isend L || l_isvar L.
  Proof.
    elim: G L=>//=.
    - by move=> L /eqP-[<-].
    - by move=> v L /eqP-[<-].
    - move=> G Ih L; case PRJ: project=>[L'|]//.
      move: PRJ=>/eqP-PRJ EQ Part; move: (Ih _ PRJ Part)=>L'end.
      move: EQ; case: ifP=>//=; [move=> _ /eqP-[<-]//| ].
      by move=> _ /eqP-[<-]/=.
    - move=> q r Ks Ih L; rewrite -/prj_all; case PRJ: prj_all=>[KsL|]//.
      move=> EQ Part; move: Part EQ.
      rewrite !in_cons !negb_or=>/andP-[p_ne_q /andP-[p_ne_r p_nin]].
      move: p_nin=>/flatten_notin/member_map-NIN.
      case: ifP=>//q_ne_r; rewrite [in q == p]eq_sym (negPf p_ne_q).
      rewrite [in r == p]eq_sym (negPf p_ne_r) => /eqP-MRG.
      move: (prjall_merge_cons PRJ MRG)=>[K mem].
      apply: (Ih K mem); last by apply/NIN.
      by move: MRG=>/eqP-MRG; move: PRJ=>/eqP/prjall_merge/( _ MRG K mem).
  Qed.

  Lemma project_parts_end p G L :
    project G p == Some L ->
    l_isend L || l_isvar L ->
    p \notin participants G.
  Proof.
    elim: G L=>//.
    - move=> G Ih L /=; case PRJ: project=>[L'|//]; move: PRJ =>/eqP-PRJ.
      case: ifP=>//.
      + move=> /lbinds_isvar-L'var _ _; apply/(Ih L')=>//.
        by rewrite L'var orbT.
      + by move=> _ /eqP-[<-]/=; apply/Ih.
    - move=>q r Ks Ih L/=; rewrite -/prj_all.
      case PRJ: prj_all=>[KsL|//]; case: ifP=>//q_r.
      case: ifP=>[_ /eqP-[<-]//|qp]; case: ifP=>[_ /eqP-[<-]//|rp].
      move=>MRG H; rewrite !in_cons eq_sym qp eq_sym rp /=.
      move: PRJ=>/eqP-PRJ; move: (prjall_merge PRJ MRG) => PRJALL.
      move=> {MRG PRJ q_r qp rp KsL}.
      move: Ih=>/(_ _ _ L (PRJALL _ _) H)-Ih {PRJALL H}.
      elim: Ks Ih=>// K Ks Ih /= H.
      rewrite mem_cat negb_or H /= ?Ih //; [|left|left] =>//.
      by move=> p' M1 M2; apply/H; right.
  Qed.

  Lemma project_parts p G L :
    g_closed G ->
    project G p == Some L ->
    p \notin participants G <->
    l_isend L.
  Proof.
    move=> cG PRJ; split.
    + move=>pG; move: (gclosed_lclosed cG PRJ)=>cL.
      move: (project_guarded PRJ) (project_parts' PRJ pG)=> gL.
      by rewrite (guarded_closed_notvar cL gL) orbC.
    + by move=>H; apply/(project_parts_end PRJ); rewrite H.
  Qed.

  Lemma project_parts_in p G L :
    g_closed G ->
    project G p == Some L ->
    ~~ l_isend L <->
    p \in participants G.
  Proof.
    move=> cG pG; split.
    - by move=> /negPf; apply/contraFT=>/(project_parts cG pG).
    - by move=>P; apply/negPf; move:P; apply/contraTF=>/(project_parts cG pG).
  Qed.

  Lemma lunroll_end L CL : LUnroll L CL -> l_isend L -> CL = rl_end.
  Proof.
    move=> LU /keep_unrolling-[k END]; move: LU=>/(LUnroll_ind k).
    by move: END=><-; apply/lunroll_end.
  Qed.

  Lemma merge_equal (A : eqType) (L : A) Ks :
    merge L [seq K.cnt | K <- Ks] = Some L ->
    forall (K : (lbl * (mty  *A))), member K Ks -> K.cnt = L.
  Proof.
    elim: Ks=>//= K Ks Ih; case: ifP=>//.
    by move=>/eqP-Kl /Ih-{}Ih K0 [->|/Ih].
  Qed.

  Notation CIH4 X Y H1 H2 H3 H4
    := (ex_intro (fun=>_) X (ex_intro (fun=>_) Y (conj H1 (conj H2 (conj H3 H4))))).
  Lemma project_wf G p L CG :
    g_closed G ->
    guarded 0 G ->
    project G p == Some L ->
    GUnroll G CG -> WF CG.
  Proof.
    move=>H1 H2 H3 H4; move: (CIH4 L G H1 H2 H3 H4)=> {H1 H2 H3 H4 G L}.
    move: CG; apply/paco1_acc=>r _ /(_ _ (CIH4 _ _ _ _ _ _))-CIH.
    move=> CG [L] [G] [cG [gG [PRJ GU]]]; apply/paco1_fold.
    move: (unroll_guarded cG gG); move: PRJ=>/eqP-PRJ.
    move: (project_unroll (rec_depth G) cG PRJ)=>[n1][n2][L'][{}PRJ] _.
    move: GU=>/(GUnroll_ind (rec_depth G)); move: PRJ.
    move: gG=>/(g_guarded_nunroll (rec_depth G) cG).
    move: cG=>/(g_closed_unroll (rec_depth G)).
    move: (n_unroll (rec_depth G) G) => {}G; move: L'=>{}L {n1 n2}.
    case: G =>/=; rewrite -/prj_all.
    - by move=>_ _ _  /gunroll_unfold; elim/gunr_inv=>//; constructor.
    - by move=>v /=; rewrite /g_closed/= -cardfs_eq0 cardfs1.
    - by move=>G _ _ _ _ /(_ G); rewrite eq_refl.
    - rewrite /g_closed; move=> F T C /= /fsetUs_fset0/member_map-cC.
      move=>/forallbP/forall_member-gG.
      case PRJ: prj_all =>[L'|//]; move: PRJ=>/eqP-PRJ.
      case: ifP=>// FT _; move=>/gunroll_unfold.
      elim/gunr_inv => // _ F' T' C' CC UA E1 _ _ {CG}.
      move: E1 UA=>[->->->] UA {F' T' C'}; constructor; rewrite ?FT//.
      * move=> l Ty G CCl; right; move: (unroll_all_exists_i UA CCl)=>[K][M][_]GU.
        move: (prjall_some PRJ M)=> [L0][_]/eqP-{}PRJ.
        by apply: (CIH _ _ _ (cC _ M) (gG _ M) PRJ GU).
      * by case: UA=>[ l Ty IG CG _|l Ty IG CG iC cCONT _ _]; exists l, Ty, CG;
                       rewrite /extend eq_refl.
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
    case: (boolP (r \notin participants G)); [| rewrite negbK].
    - move=> PARTS nvG; move: iPrj=>/eqP-iPrj.
      move: (proj1 (project_parts cG iPrj) PARTS)=> endL.
      move: (lunroll_end LU endL)=>->; apply/paco2_fold.
      constructor; first by move=>/(partof_unroll cG gG GU)-P'; move: P' PARTS=>->.
      by apply/(project_wf cG gG iPrj).
    - case: G cG gG nrG iPrj GU=>//;
              first by move=> GT _ _ /(_ GT); rewrite eq_refl.
      move=>FROM TO CONT; rewrite project_msg /g_closed/=.
      move=>/fsetUs_fset0/member_map-cG /forallbP/forall_member-gG _ I_prj GU PARTS _.
      move: GU; move=>/gunroll_unfold.
      case E: _ _/ =>// [FROM' TO' CONT' CC GU].
      move: E GU=> [<-<-<-] {FROM' TO' CONT'} GU.
      apply/paco2_fold; move: I_prj.
      case E: prj_all=>[KsL|]//; case:ifP=>// F_neq_T.
      case:ifP=>[F_r | F_ne_r].
      + move=>[EL]; move: EL LU=><- {L} /lu_unfold-LU.
        case EL: _ _/LU=>[||a p Ks C LU]//; move: EL LU=>[<-<-<-] LU {a p Ks}.
        move: F_r CIH E=>/eqP<- CIH E; apply/prj_send; first by apply/negPf.
        * by apply (cproj_samedom GU LU E).
        * by apply/(cproj_all CIH cG gG GU LU).
      + case:ifP=>[T_r | T_ne_r].
        * move=>[EL]; move: EL LU=><- {L} /lu_unfold-LU {F_ne_r}.
          case EL: _ _/LU=>[||a p Ks C LU]//; move: EL LU=>[<-<-<-] LU {a p Ks}.
          move: T_r CIH E=>/eqP<- CIH E.
          apply/prj_recv; first by rewrite eq_sym (F_neq_T).
          - by apply (cproj_samedom GU LU E).
          - by apply/(cproj_all CIH cG gG GU LU).
        * move=> MRG.
          have M: merge L [seq K.cnt | K <- KsL] = Some L
            by move: MRG=>{E}; case: KsL=>//=K Ks /eqP-M;
               move: (merge_some M)=>E; move: E M=>->; rewrite eq_refl=>/eqP.
          move: (lunroll_merge LU E M)=>[CCL [{LU}LU cMRG]].
          move: F_ne_r T_ne_r; rewrite eq_sym=>F_ne_r; rewrite eq_sym=>T_ne_r.
          apply: prj_mrg;rewrite ?F_ne_r ?T_ne_r ?F_neq_T//; last by apply:cMRG.
          - elim/gunrall_inv: GU=> // _.
            + move=> l Ty Gl CGl _ _; exists l, Ty, CGl.
              by rewrite /extend eq_refl.
            + move=> l Ty Gl CGl Cl CCl _ _ _ _; exists l, Ty, CGl.
              by rewrite /extend eq_refl.
          - move: E MRG=>/eqP-E /eqP-MRG; move: (prjall_merge E MRG)=> ALL_EQ.
            move=> l Ty G CCl.
            move: (unroll_all_exists_i GU CCl)=>[K'] [MEM] [_] GU'.
            move: (ALL_EQ _ MEM) (cG _ MEM)=>PK cK.
            move: PARTS; rewrite !in_cons F_ne_r T_ne_r /= => PARTS.
            move: PARTS=> /flatten_mapP-[K] /memberP-K_CONT r_in_K.
            move: ((project_parts_in (cG _ K_CONT) (ALL_EQ _ K_CONT)).2 r_in_K).
            rewrite (project_depth cK PK)=>[][m] H.
            by apply/(partof_all_unroll cK GU' PK)/H.
          - by apply (cproj_samedom GU LU E).
          - by apply/(cproj_all CIH cG gG GU LU)=>//.
  Qed.

  Theorem ic_proj r :
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

    move: CIH =>/(_ _ _ (ex_intro _ _ (ex_intro _ _
                          (conj _ (conj _ (conj _ (conj _ _)))))))-CIH.
    move=> cG cL [iG] [cG'] [ciG] [giG] [iGiL] [GU LU].

    move: iGiL  => /eqP-iGiL.
    move: (project_unroll (rec_depth iG) ciG iGiL) => [U1] [U2] [L] [proj] U12.
    move: LU =>/(LUnroll_ind U1); move: U12=>->; rewrite -LUnroll_ind=>UL.
    move : GU (unroll_guarded ciG giG)=>/(GUnroll_ind (rec_depth iG))=>GU nrG.
    move: (g_guarded_nunroll (rec_depth iG) ciG giG)=>guiG.
    move: (g_closed_unroll (rec_depth iG) ciG)=>cuiG {ciG giG iGiL}.
    by apply/(project_nonrec CIH cuiG guiG nrG proj).
  Qed.

  Inductive IProj (p : role) : ig_ty -> rl_ty -> Prop :=
  | iprj_end CG CL :
      Project p CG CL ->
      IProj p (ig_end CG) CL
  | iprj_send1 q KsG KsL :
      p != q ->
      same_dom KsG KsL ->
      R_all (IProj p) KsG KsL ->
      IProj p (ig_msg None p q KsG) (rl_msg l_send q KsL)
  | iprj_send2 l t q r KsG KsL L :
      p != r ->
      q != r ->
      same_dom KsG KsL ->
      R_all (IProj p) KsG KsL ->
      KsL l = Some (t, L) ->
      IProj p (ig_msg (Some l) q r KsG) L
  | iprj_recv o q KsG KsL :
      p != q ->
      same_dom KsG KsL ->
      R_all (IProj p) KsG KsL ->
      IProj p (ig_msg o q p KsG) (rl_msg l_recv q KsL)
  (* | prj_end2 G : ~ In r G -> Proj_ r G rl_end *)
  | iprj_mrg q s KsG KsL L :
      q != s ->
      p != q ->
      p != s ->
      (* InAll r KsG -> *)
      (exists l Ty G, KsG l = Some (Ty, G)) ->
      same_dom KsG KsL ->
      R_all (IProj p) KsG KsL ->
      Merge KsL L ->
      IProj p (ig_msg None q s KsG) L
  .





  Lemma IProj_end_inv_aux p GG CG CL:
    IProj p GG CL -> GG = ig_end CG ->
    Project p CG CL.
  Proof.
  by case=>//; move=> CG0 CL0 ipro [CGeq]; rewrite -CGeq.
  Qed.

  Lemma IProj_end_inv p CG CL:
    IProj p (ig_end CG) CL -> Project p CG CL.
  Proof.
  by move=> hp; apply (IProj_end_inv_aux hp).
  Qed.

  Lemma IProj_send1_inv_aux F T C GG CL:
    IProj F GG CL -> GG = (ig_msg None F T C) ->
    F != T /\ (exists lC, CL = rl_msg l_send T lC /\
    same_dom C lC /\ R_all (IProj F) C lC).
  Proof.
  case=>//.
  + move=> q gC lC neq samedom rall [eq1 eq2].
    by rewrite -eq1 -eq2; split; [| exists lC;  split; [ |]].
  + move=> o q gC lC neq samedom rall [eq1 eq2 eq3 eq4].
    by move: neq; rewrite eq2 -(rwP negP).
  + move=> q s gC lC L neq1 neq2 neq3 NE samedom rall mer [eq1 eq2 eq3].
    by move: neq2; rewrite eq1 eq_refl.
  Qed.

  Lemma IProj_send1_inv F T C CL:
    IProj F (ig_msg None F T C) CL ->
    F != T /\ (exists lC, CL = rl_msg l_send T lC /\
    same_dom C lC /\ R_all (IProj F) C lC).
  Proof.
  by move=> hp; apply: (IProj_send1_inv_aux hp).
  Qed.


  Lemma IProj_send2_inv_aux L p F T C GG CL:
    IProj p GG CL -> GG = (ig_msg (Some L) F T C) -> p != T ->
    F != T /\ (exists lC Ty, lC L = Some (Ty, CL) /\
    same_dom C lC /\ R_all (IProj p) C lC).
  Proof.
  case=>//.
  + move=> l Ty q r gC lC CL0 neq1 neq2 samedom rall Cleq [<-<-<-<-] neq3.
    by split=>//; exists lC, Ty; split.
  + move=> o q gC lC neq samedom rall [_ <-<-<-] {o F T C}.
    by rewrite eq_refl.
  Qed.

  Lemma IProj_send2_inv L p F T C CL:
    IProj p (ig_msg (Some L) F T C) CL -> p != T ->
    F != T /\ (exists lC Ty, lC L = Some (Ty, CL) /\
    same_dom C lC /\ R_all (IProj p) C lC).
  Proof.
  by move=> hp; apply: (IProj_send2_inv_aux hp).
  Qed.

 Lemma IProj_recv_inv_aux olb F T C GG CL:
    IProj T GG CL -> GG = (ig_msg olb F T C) ->
    F != T /\ (exists lC, CL = rl_msg l_recv F lC /\
    same_dom C lC /\ R_all (IProj T) C lC).
  Proof.
  case =>//.
  + move=> q gC lC neq samedom rall [eq1 eq2 eq3].
    by move: neq; rewrite eq3 -(rwP negP).
  + move=> l Ty q r cG cL L neq1 _ _ _ _ [_ _ eq1].
    by move: eq1 neq1=>->/eqP.
  + move=> o q gC lC neq samedom rall [eq1 eq2 eq3].
    by rewrite -eq2 -eq3; split; [rewrite eq_sym| exists lC; split; [ | split; [|]]].
  + move=> q s gC lC L neq1 neq2 neq3 NE samedom rall mer [eq1 eq2 eq3 eq4].
    by move: neq3; rewrite eq3 -(rwP negP).
  Qed.

  Lemma IProj_recv_inv olb F T C CL:
    IProj T (ig_msg olb F T C) CL ->
    F != T /\ (exists lC, CL = rl_msg l_recv F lC /\
    same_dom C lC /\ R_all (IProj T) C lC).
  Proof.
  by move=> hp; apply: (IProj_recv_inv_aux hp).
  Qed.

  Lemma IProj_mrg_inv_aux p F T C GG CL:
    IProj p GG CL ->
    p != F -> p != T -> GG = ig_msg None F T C ->
    F != T /\ (exists lC, same_dom C lC /\
      R_all (IProj p) C lC /\
      Merge lC CL).
  Proof.
  case =>//.
  + move=> q gC lC neq samedom rall neqF neqT [eq1 eq2 eq3].
    by move: neqF; rewrite eq1 -(rwP negP).
  + case=>// q cG cL neq samedom rall neqF neqT [eq1 eq2 eq3].
    by move: neqT; rewrite eq2 -(rwP negP).
  + move=>q s gC lC CL0 neq1 neq2 neq3 NE samedom rall mer neqF neqT [eq1 eq2 eq3].
    split; [by move: neq1; rewrite eq1 eq2|exists lC].
    by rewrite -eq3; split; [ |split; [|]].
  Qed.

  Lemma IProj_mrg_inv p F T C CL:
    IProj p (ig_msg None F T C) CL ->
    p != F -> p != T ->
    F != T /\ (exists lC, same_dom C lC /\
      R_all (IProj p) C lC /\
      Merge lC CL).
  Proof.
  by move=> hp neq1 neq2; apply: (IProj_mrg_inv_aux hp neq1 neq2).
  Qed.



  Lemma EqL_IProj p G lT lT':
    IProj p G lT -> EqL lT lT' -> IProj p G lT'.
  Proof.
  move=> hp; move: hp lT'; elim.
  + move=> CG {}lT Pro lT' eqL; apply: iprj_end.
    by apply: (EqL_Project eqL Pro).
  + move=> q C lC neq samed rall Ih lT' eqL.
    move: (EqL_l_msg_inv eqL); elim=> lC'; elim=> samedom.
    elim=> rall' ->; apply: (iprj_send1 neq).
    * by move=> L Ty; rewrite (samed L Ty).
    * move=> L Ty G0 lT0' CL lCL'.
      move: (samedom L Ty); elim=> _.
      elim; [move=> lT0 lCL | by exists lT0'].
      apply: (Ih _ _ _ _ CL lCL).
      by apply: (rall' _ _ _ _ lCL lCL').
  + move=> L Ty q r C lC lT0 neq1 neq2 samed rall Ih lCL lT0' eqL.
    move:(samed L Ty);elim=> _;elim;[move=> G0 CL|by exists lT0].
    apply: (@iprj_send2 p L Ty q r C (extend L (Ty, lT0') lC) _ neq1 neq2).
    * apply: (same_dom_extend_some_l _ samed CL).
    * move=> LL TTy GG lTT CLL; rewrite /extend; case: ifP.
      - rewrite -(rwP eqP); move=> eqLL [eqTy eqlT0'].
        rewrite -eqlT0'; rewrite -eqLL in CLL.
        move: CLL; rewrite CL; move=> [_ eqG0]; rewrite -eqG0.
        by apply: (Ih _ _ _ _ CL lCL).
      - by move=> neqLL lCLL; apply: rall CLL lCLL.
    * by rewrite /extend; case: ifP =>//; rewrite eq_refl //.
  + move=> o q C lC neq samed rall Ih lT' eqL.
    move: (EqL_l_msg_inv eqL); elim=> lC'; elim=> samedom.
    elim=> rall' ->; apply: (iprj_recv o neq).
    * by move=> L Ty; rewrite (samed L Ty).
    * move=> L Ty G0 lT0' CL lCL'.
      move: (samedom L Ty); elim=> _.
      elim; [move=> lT0 lCL | by exists lT0'].
      apply: (Ih _ _ _ _ CL lCL).
      by apply: (rall' _ _ _ _ lCL lCL').
  + move=> q s C lC lT0 neqqs neqpq neqps NE samed rall Ih mer lT' eqL.
    apply: (@iprj_mrg _ _ _ _
          (same_dom_const C lT') _ neqqs neqpq neqps)=>//.
    * by apply: same_dom_const_same_dom.
    * move=> L Ty G0 lTT' CL sdLa.
      move: (same_dom_const_some sdLa)=>->.
      move: (samed L Ty); elim=> sam _; move: sam.
      elim; [move=> lTT lCL | by exists G0].
      by apply: (Ih _ _ _ _ CL lCL) (EqL_trans (mer _ _ _ lCL) eqL).
    * move=> Ln Tn lTn sdc; move: (same_dom_const_some sdc) =>-> //=.
  Qed.



End CProject.
