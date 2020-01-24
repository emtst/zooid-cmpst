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

  Fixpoint partial_proj d (l : l_ty) (r : role) : option s_ty :=
    match l with
    | l_end => Some (s_end)
    | l_var v => Some (s_var v)
    | l_rec L =>
      match partial_proj d.+1 L r with
      | Some s => Some (if s is s_var v
                        then if v <= d then s_end
                             else s_rec s
                        else s_rec s)
      | _ => None
      end
    | l_msg a p Ks =>
      match (fix prj_all d Ks r :=
               match Ks with
               | [::] => Some [::]
               | K::Ks =>
                 match partial_proj d K.cnt r, prj_all d Ks r with
                 | Some s, Some Ks => Some ((K.lbl, (K.mty, s)) :: Ks)
                 | _, _ => None
                 end
               end
            ) d Ks r with
      | Some Ks => if p == r then Some (s_msg a Ks)
                   else merge_all [seq K.cnt | K <- Ks]
      | None => None
      end
    end.

  Fixpoint pprj_all d (Ks : seq (lbl * (mty * l_ty))) (r : role)
    : option (seq (lbl * (mty * s_ty))) :=
    match Ks with
    | [::] => Some [::]
    | K::Ks => match partial_proj d K.cnt r, pprj_all d Ks r with
               | Some s, Some Ks => Some ((K.lbl, (K.mty, s)) :: Ks)
               | _, _ => None
               end
    end.

  Lemma partialproj_all d a p Ks r
    : partial_proj d (l_msg a p Ks) r =
      match pprj_all d Ks r with
      | Some Ks' => if p == r then Some (s_msg a Ks')
                    else merge_all [seq K.cnt | K <- Ks']
      | None => None
      end.
  Proof. by []. Qed.

  Fixpoint project (d : nat) (g : g_ty) (r : role) : option l_ty :=
    match g with
    | g_end => Some l_end
    | g_var v => Some (l_var v)
    | g_rec G =>
      match project d.+1 G r with
      | Some L => Some (if L is l_var v
                        then if v <= d then l_end
                             else l_rec L
                        else l_rec L)
      | None => None
      end
    | g_msg p q Ks =>
      match (fix proj_all d Ks r :=
               match Ks with
               | [::] => Some [::]
               | K::Ks =>
                 match project d K.cnt r, proj_all d Ks r with
                 | Some L, Some Ks => Some ((K.lbl, (K.mty, L)) :: Ks)
                 | _, _ => None
                 end
               end
            ) d Ks r with
      | Some Ks => if p == q then None
                   else if p == r then Some (l_msg l_send q Ks)
                        else if q == r then Some (l_msg l_recv p Ks)
                             else merge_all [seq K.cnt | K <- Ks]
      | None => None
      end
    end.

  Fixpoint prj_all d (Ks : seq (lbl * (mty * g_ty))) (r : role)
    : option (seq (lbl * (mty * l_ty))) :=
    match Ks with
    | [::] => Some [::]
    | K::Ks => match project d K.cnt r, prj_all d Ks r with
               | Some L, Some Ks => Some ((K.lbl, (K.mty, L)) :: Ks)
               | _, _ => None
               end
    end.

  Lemma project_msg d p q Ks r
    : project d (g_msg p q Ks) r =
      match prj_all d Ks r with
      | Some Ks' => if p == q then None
                   else if p == r then Some (l_msg l_send q Ks')
                        else if q == r then Some (l_msg l_recv p Ks')
                             else merge_all [seq K.cnt | K <- Ks']
      | None => None
      end.
  Proof. by []. Qed.

  Lemma prjall_some d p Ks Ks' :
    prj_all d Ks p == Some Ks' ->
    forall K, member K Ks ->
              exists L, member (K.lbl, (K.mty, L)) Ks' /\
                        project d K.cnt p = Some L.
  Proof.
    elim: Ks => [|K Ks Ih]//= in Ks' *.
    case Kp: project => [Lp|//].
    case Ksp: prj_all => [LKs|//]; move: Ksp=>/eqP-Ksp.
    move=> /eqP-[Eq]; move: Eq Ih =><- Ih {Ks'} K0 [->{K0}|].
    - by exists Lp; split=>//=; left.
    - by move=> /(Ih LKs Ksp K0)-[L [L_LKs PrjL]]; exists L; split=>//=; right.
  Qed.

  Lemma prjall_some2 d p Ks Ks' :
    prj_all d Ks p == Some Ks' ->
    forall K, member K Ks' ->
              exists G, member (K.lbl, (K.mty, G)) Ks /\
                        project d G p = Some K.cnt.
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

  Definition full_project d G p q :=
    match project d G p with
    | Some L => partial_proj d L q
    | None => None
    end.

  Definition fullproj_all d Ks p q :=
    match prj_all d Ks p with
    | Some LKs => pprj_all d LKs q
    | None => None
    end.

  Lemma fullproject_some d p q G L S
    : project d G p == Some L -> partial_proj d L q == Some S ->
      full_project d G p q = Some S.
  Proof. by rewrite /full_project =>/eqP-> /eqP. Qed.

  Lemma def_fprojall d p q G L S
    : prj_all d G p == Some L -> pprj_all d L q == Some S ->
      fullproj_all d G p q = Some S.
  Proof. by rewrite /fullproj_all =>/eqP-> /eqP. Qed.


  Lemma dualproj_msg d Ks p q Ks0 Ks1 S S' a1 a2 :
    (forall d (s s0 : seq (lbl * (mty * s_ty))),
        fullproj_all d Ks p q == Some s ->
        fullproj_all d Ks q p == Some s0 ->
        s0 = [seq (x.lbl, (x.mty, dual x.cnt)) | x <- s]) ->
    a2 == dual_act a1 ->
    prj_all d Ks p = Some Ks0 ->
    prj_all d Ks q = Some Ks1 ->
    partial_proj d (l_msg a1 q Ks0) q == Some S ->
    partial_proj d (l_msg a2 p Ks1) p == Some S' ->
    S' = dual S.
  Proof.
    move=> Ih /eqP-a12 Lp Lq; rewrite !partialproj_all !eq_refl.
    case Kspq: pprj_all => [Ks0'|//].
    case Ksqp: pprj_all => [Ks1'|//].
    move=> /eqP-[<-]/eqP-[<-]/=; congr s_msg=>//.
    by rewrite (Ih d Ks0' Ks1') /fullproj_all ?Lp ?Kspq ?Lq ?Ksqp.
  Qed.

  Lemma merge_some (A : eqType)
        (K : lbl * (mty * A))
        (Ks : seq (lbl * (mty * A))) L
    : merge K.cnt [seq K0.cnt | K0 <- Ks] == Some L -> K.cnt = L.
  Proof. by elim: Ks=>[/eqP-[]//|K' Ks Ih/=]; case:ifP. Qed.

  Lemma merge_pprj d L' Ks L p S
    : merge L' [seq K.cnt | K <- Ks] == Some L -> partial_proj d L p == Some S ->
      exists Ks', pprj_all d Ks p = Some Ks' /\
                  merge S [seq K.cnt | K <- Ks'] = Some S.
  Proof.
    elim: Ks=>[_|K' Ks Ih]/=; first (by exists [::]; split); move: Ih.
    case: ifP=>///eqP<- Ih M_L'; move: (merge_some M_L')=>-> /eqP-L_S.
    rewrite L_S; move: L_S=>/eqP-L_S; move: (Ih M_L' L_S) => [Ks' [Ksp M_S]].
    by exists ((K'.lbl, (K'.mty, S)):: Ks'); rewrite Ksp /= eq_refl M_S.
  Qed.

  Lemma mergeall_pprj d Ks L p S
    : merge_all [seq K.cnt | K <- Ks] == Some L -> partial_proj d L p == Some S ->
      exists Ks', pprj_all d Ks p = Some Ks' /\
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

  Lemma dualproj_all d Ks p q Ks0 Ks1 S S' s a :
    (forall s s0 : seq (lbl * (mty * s_ty)),
        fullproj_all d Ks p q == Some s ->
        fullproj_all d Ks q p == Some s0 ->
        s0 = [seq (x.lbl, (x.mty, dual x.cnt)) | x <- s]) ->
    prj_all d Ks p = Some Ks0 ->
    prj_all d Ks q = Some Ks1 ->
    (s == q) = false ->
    partial_proj d (l_msg a s Ks0) q == Some S ->
    match merge_all [seq K.cnt | K <- Ks1] with
    | Some L => partial_proj d L p
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

  Lemma dualproj_all2 d Ks p q Ks0 Ks1 S S' s a :
    (forall s s0 : seq (lbl * (mty * s_ty)),
        fullproj_all d Ks p q == Some s ->
        fullproj_all d Ks q p == Some s0 ->
        s0 = [seq (x.lbl, (x.mty, dual x.cnt)) | x <- s]) ->
    prj_all d Ks p = Some Ks0 ->
    prj_all d Ks q = Some Ks1 ->
    (s == p) = false ->
    match merge_all [seq K.cnt | K <- Ks0] with
    | Some L => partial_proj d L q
    | None => None
    end == Some S ->
    partial_proj d (l_msg a s Ks1) p == Some S' ->
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

  Lemma fprojall_eq d Ks p q Ks0 Ks1
    : (forall K, member K Ks ->
                 forall d S S', full_project d K.cnt p q == Some S ->
                                full_project d K.cnt q p == Some S' ->
                                S' = dual S) ->
      fullproj_all d Ks p q == Some Ks0 ->
      fullproj_all d Ks q p == Some Ks1 ->
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
      rewrite -(H K _ d Sp Sq) /full_project ?Kp ?Ep ?Kq ?Eq //; last (by left).
      congr cons; apply/Ih; rewrite /fullproj_all ?Ksp ?Esp ?Ksq ?Esq//.
      by move=> K0 K0Ks; apply/H; right.
  Qed.

  Lemma prjall_merge d p Ks KsL L :
    prj_all d Ks p == Some KsL ->
    merge_all [seq K0.cnt | K0 <- KsL] == Some L ->
    forall K, member K Ks -> project d K.cnt p == Some L.
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

  (* Lemma project_var_notin d p G v L : *)
  (*   (L == l_end) || (L == l_var v) -> *)
  (*   project d G p == Some L -> *)
  (*   p \notin participants G. *)
  (* Proof. *)
  (*   elim/gty_ind1: G => [|v'|G Ih|q r Ks Ih]// in d L v *. *)
  (*   - move: Ih=>/=; case: project =>[Lp|//] Ih. *)
  (*     move=>/orP-[/eqP->|/eqP->]; case: ifP=>[/eqP-Lp_var|]//. *)
  (*     move: Lp_var Ih=>-> /(_ (l_var 0) 0); rewrite eq_refl/==>Ih. *)
  (*     by apply: Ih. *)
  (*   - rewrite project_msg; case E: (prj_all _ _)=>[KsL|//]; move: E=>/eqP-E/=. *)
  (*     case: ifP=>[//|/(rwP negPf)-q_ne_r]. *)
  (*     case: ifP=>[/eqP->/orP-[/eqP->|/eqP->]//|/(rwP negPf)-q_ne_p]. *)
  (*     case: ifP=>[/eqP->/orP-[/eqP->|/eqP->]//|/(rwP negPf)-r_ne_p]. *)
  (*     do 2 rewrite in_cons negb_or; move=> L_end_var M_some. *)
  (*     do 2 rewrite eq_sym ?q_ne_p /= ?r_ne_p /=; move: M_some. *)
  (*     move: E=>/prjall_merge-E /E-Prjall. *)
  (*     apply/flatten_mapP=>[[Kg /memberP-M]]. *)
  (*     by apply/negP; apply: (Ih _ M L v L_end_var); apply: Prjall. *)
  (* Qed. *)

  Lemma projectmsg_var d n p r s Ks :
    project d (g_msg r s Ks) p == Some (l_var n) ->
    r != p /\ s != p /\ r != s /\
    (forall K, member K Ks -> project d K.cnt p == Some (l_var n)).
  Proof.
    rewrite project_msg; case Ksp: prj_all => [Ks'|//]; move: Ksp=>/eqP.
    do ! case: ifP=>//; move=>s_ne_p r_ne_p r_ne_s.
    by move=>/prjall_merge-H /H.
  Qed.

  Lemma pprjall_merge d p Ks KsL L :
    pprj_all d Ks p == Some KsL ->
    merge_all [seq K0.cnt | K0 <- KsL] == Some L ->
    forall K, member K Ks -> partial_proj d K.cnt p == Some L.
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

  Lemma pprjall_some d p Ks Ks' :
    pprj_all d Ks p == Some Ks' ->
    forall K,
      member K Ks ->
      exists L, member (K.lbl, (K.mty, L)) Ks' /\ partial_proj d K.cnt p = Some L.
  Proof.
    elim: Ks=>//= Kl Ks Ih in Ks' *.
    case Kl_p: partial_proj=>[s|//].
    case Ks_p: pprj_all=>[Ks0|//]; move: Ks_p=>/eqP/Ih-{Ih} Ih.
    move=>/eqP-[<-] K [E|/Ih-{Ih}[s' [M Kp]]]{Ks'}.
    - by move: E Kl_p=><- {Kl}; exists s; split=>//; left.
    - by exists s'; split=>//; right.
  Qed.

  Lemma pproj_var d n p q G Lq Sq :
    project d G p == Some (l_var n) ->
    project d G q == Some Lq ->
    partial_proj d Lq p == Some Sq ->
    Sq = s_var n.
  Proof.
    elim/gty_ind1: G =>[//|v//=|G Ih//=|r s Ks Ih] in d Lq Sq *.
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
        by move: Mrg Ih => /(_ _ ML)-Pprj /(_ _ KKs d L Sq Kp KL Pprj).
      * rewrite partialproj_all (negPf r_ne_p); case E: pprj_all=>[KsS|//] Mrg.
        have [K KKs]: exists K, member K Ks
            by move=>{Ih Ksp}; case: Ks Prj_Ks E Mrg;
                       first (by move=>/eqP-[<-] [<-]);
                       move=> K; exists K; left.
        move: E Mrg Prj_Ks =>/eqP-E /(pprjall_merge E)-Mrg /prjall_some-Prj_Ks.
        move:Prj_Ks Ksp =>/(_ K KKs)-[L [ML /eqP-KL]] /(_ K KKs)-Kp.
        by move: Mrg Ih => /(_ _ ML)-Pprj /(_ _ KKs d L Sq Kp KL Pprj).
      * move=> Mrg PPrj.
        suff : exists K, member K Ks by
              move=>[K M]; move: Mrg=>/(prjall_merge Prj_Ks)-Ksq{Prj_Ks};
                      move: Ih=>/(_ K M d _ _ (Ksp _ M) (Ksq _ M) PPrj)-Ih.
        case: Ks Prj_Ks {Ih Ksp}=>[//=|K Ks _]; last (by exists K; left).
        by move=>/eqP-[Eq]; move: Eq Mrg=><-.
  Qed.

  Lemma proj_var_eq d G p q v v':
    project d G p == Some (l_var v) ->
    project d G q == Some (l_var v') ->
    v == v'.
  Proof.
    elim/gty_ind1: G => [|n|G Ih|f t Ks Ih]// in d v v' *.
    - by move=>/eqP-[<-]/eqP-[<-].
    - move=>/=.
      case Pp: project =>[Lp|//]; move: Pp=>/eqP=>Pp.
      case Pq: project =>[Lq|//]; move: Pq=>/eqP=>Pq.
      case: Lp Pp=>//v1 Pp.
      case: Lq Pq=>//v2 Pq.
      move: (Ih d.+1 _ _ Pp Pq) =>/eqP->.
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

  Lemma all_compat d G S S' p q :
    p != q ->
    full_project d G p q == Some S ->
    full_project d G q p == Some S' ->
    S' = dual S.
  Proof.
    move=>/negPf-p_neq_q.
    elim/gty_ind1: G => [|v|G Ih| r s Ks Ih] in d S S' *.
    - by do ! (move=>/eqP-[<-]).
    - by do ! (move=>/eqP-[<-]).
    - rewrite /full_project/=.
      case Ep: project=>[Lp|//]; case Eq: project=>[Lq|//].
      have DEC: forall L, (exists v, L == l_var v) \/ (forall v, L != l_var v)
          by case; try (by right); move=> v; left; exists v; apply/eqP.
      move: (DEC Lp) Ep Eq =>[[vp /eqP->]|Lp_n_var];
      move: (DEC Lq) =>[[vq /eqP->]|Lq_n_var]/=;
      rewrite ?(@lty_not_var l_ty _ _ _ Lq_n_var)
              ?(@lty_not_var l_ty _ _ _ Lp_n_var).
      * move=> /eqP-P1 /eqP-P2; move: (proj_var_eq P1 P2)=>/eqP->.
        by case: ifP=>//= _ /eqP-[<-] /eqP-[<-] //; case: ifP.
      * case: ifP=>[vp_d|d_vp]/=; [|rewrite d_vp].
        + case Eq: partial_proj=>[Sq|//]; move: Eq=>/eqP-Eq.
          move=>/eqP-Ep /eqP-ELq; move: (pproj_var Ep ELq Eq)=>->; rewrite vp_d.
          by move=>/eqP-[<-]/eqP-[<-].
        + case Eq: partial_proj=>[Sq|//]; move: Eq=>/eqP-Eq.
          move=>/eqP-Ep /eqP-ELq; move: (pproj_var Ep ELq Eq)=>->; rewrite d_vp.
          by move=>/eqP-[<-]/eqP-[<-].
      * case: ifP=>[vq_d|d_vq]/=; [|rewrite d_vq].
        + case Ep: partial_proj=>[Sp|//]; move: Ep=>/eqP-Ep.
          move=>/eqP-Eq /eqP-ELq; move: (pproj_var ELq Eq Ep)=>->; rewrite vq_d.
          by move=>/eqP-[<-]/eqP-[<-].
        + case Ep: partial_proj=>[Sp|//]; move: Ep=>/eqP-Ep.
          move=>/eqP-Eq /eqP-ELq; move: (pproj_var ELq Eq Ep)=>->; rewrite d_vq.
          by move=>/eqP-[<-]/eqP-[<-].
      * move=>/= {DEC}.
        case Ep: partial_proj=>[Sp|]//; move: Ep=>/eqP-Ep.
        case Eq: partial_proj=>[Sq|]//; move: Eq=>/eqP-Eq.
        move=>/eqP-Prj_p /eqP-Prj_q.
        move: Prj_p Ep =>/fullproject_some-Prj_p /Prj_p/eqP/Ih-{Prj_p Ih}Ih.
        move: Prj_q Eq =>/fullproject_some-Prj_q /Prj_q/eqP/Ih-{Prj_q Ih}Ih.
        move:Ih=>-> {Sq}.
        have DEC: forall L, (exists v, L == s_var v) \/ (forall v, L != s_var v)
            by case; try (by right); move=> v; left; exists v; apply/eqP.
        move: (DEC Sp) =>[[vp /eqP->]/= /eqP-[<-]/eqP-[<-]|Sp_n_var];
         first by case: ifP.
        rewrite (@sty_not_var s_ty _ _ _ Sp_n_var).
        rewrite (@sty_not_var s_ty _ _ _ (dual_not_var Sp_n_var)).
        by move=>/eqP-[<-] /eqP-[<-].
    - move: Ih=>/fprojall_eq-Ih; rewrite /full_project !project_msg.
      case Ksp: prj_all => [Ks0|//]; case Ksq: prj_all => [Ks1|//].
      case: ifP=>// -r_neq_s.
      do ! (case: ifP=>[/eqP->|]//; rewrite ?p_neq_q ?r_neq_s //).
      * by apply: (dualproj_msg Ih).
      * by apply: (dualproj_all (Ih d)).
      * by move=> _; apply: (dualproj_msg Ih).
      * by move=> r_neq_q _; apply: (dualproj_all (Ih d)).
      * by move=> s_neq_p _; apply: (dualproj_all2 (Ih d)).
      * by move=> _ _ r_neq_p; apply: (dualproj_all2 (Ih d)).
      * case M_Ks0: (merge_all [seq K.cnt | K <- Ks0]) => [L'|//].
        case M_Ks1: (merge_all [seq K.cnt | K <- Ks1]) => [L|//].
        move: M_Ks0 M_Ks1 =>/eqP-M_Ks0 /eqP-M_Ks1 _ _ _ _ L'S LS'.
        move: (mergeall_pprj M_Ks0 L'S)=>[Ks' [/eqP-Ks0q /eqP-H]]; move: H.
        move: (mergeall_pprj M_Ks1 LS')=>[Ks'' [/eqP-Ks1p /eqP-H]]; move: H.
        rewrite (Ih d Ks' Ks'') /fullproj_all ?Ksp ?Ksq // -map_comp/comp/=.
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

  (* Lemma project_rec d G r L : *)
  (*   project d.+1 G r == Some L -> *)
  (*   ((L == l_var 0) = false) -> *)
  (*   project d (g_rec G) r = Some (l_rec L). *)
  (* Proof. move=>/=/eqP->; case: L=>//=. by move=>/=/eqP-[->] ->. Qed. *)

  Lemma gclosed_lclosed d G r L :
    g_fidx d G == fset0 ->
    project d G r == Some L ->
    l_fidx d L == fset0.
  Proof.
    elim/gty_ind1: G =>[|v|G Ih|p q Ks Ih] in d L *.
    - by move=> _ /eqP-[<-].
    - move=> /=; case: ifP; first by rewrite -cardfs_eq0 cardfs1.
      by move=> H _ /eqP-[<-]/=; rewrite H.
    - move: Ih=>/=; case Eq: project =>[Lr|//]; move: Eq=>/eqP-Eq.
      move=> /(_ d.+1 Lr)-Ih;move=>/Ih/(_ Eq) {Eq Ih}.
      case: Lr=>[|v|Lr|p q Ks]//= H /eqP-[<-]//=.
      by case: ifP=>//.
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

  Lemma prjall_open d r n g l Ks Ks' :
    (forall p : lbl * (mty * g_ty),
      member p Ks ->
      forall s : lty_eqType,
        project d p.2.2 r == Some s ->
        project d (g_open n g p.2.2) r = Some (l_open n l s)) ->
    prj_all d Ks r = Some Ks' ->
    prj_all d [seq (K.1, (K.2.1, g_open n g K.2.2)) | K <- Ks] r
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

  (* FIXME: refactor lemmas below *)
  Lemma project_closed r iG iL :
    g_closed iG ->
    project 0 iG r == Some iL ->
    l_closed iL.
  Proof.
    rewrite /l_closed/g_closed.
    elim/gty_ind1: iG iL 0 =>//.
    - by move=> iL n _ /eqP-[<-].
    - move=> v iL n /=; case: ifP; first by rewrite -cardfs_eq0 cardfs1.
      by move=>F _ /eqP-[<-]/=; rewrite F.
    - move=> G Ih iL n /=.
      case Prj: project=>[iL'|]// cG; move: Prj=>/eqP-Prj.
      case: (v_lty iL')=>[|/(@lty_not_var l_ty)->/eqP-[<-]/=]; last by apply/Ih.
      move=>[v E]; move: E Prj=>->Prj; case: ifP; first by move=> _ /eqP-[<-].
      move: (Ih _ _  cG Prj)=>/=.
      case: ifP=>//; first by rewrite -cardfs_eq0 cardfs1.
      by move=>/(rwP negPf); rewrite ltnNge negbK=>->.
    - move=>p q Ks Ih iL n; rewrite project_msg=>/=/fsetUs_fset0/member_map-cKs.
      case PrjAll: prj_all => [KsL|]//; case: ifP=>// p_n_q.
      move: PrjAll=>/eqP/prjall_some2-PrjAll.
      case: ifP=>[p_r|p_n_r]; last case: ifP=>[q_r|q_n_r].
      + move=>/eqP-[<-]/=; apply/fsetUs_fset0/member_map=>K M.
        move: (PrjAll _ M)=> [G [MG /eqP-PrjG]].
        by apply/(Ih _ MG)=>//; apply/cKs.
      + move=>/eqP-[<-]/=; apply/fsetUs_fset0/member_map=>K M.
        move: (PrjAll _ M)=> [G [MG /eqP-PrjG]].
        by apply/(Ih _ MG)=>//; apply/cKs.
      + case: KsL PrjAll=>//=K KsL PrjAll M; move: (merge_some M)=><-.
        move: (PrjAll K (or_introl erefl))=>[G [MG /eqP-PrjG]].
        by apply: (Ih _ MG)=>//; apply/cKs.
  Qed.

  (* TODO *)
  Lemma project_guarded r iG iL :
    guarded 0 iG ->
    project 0 iG r == Some iL ->
    lguarded 0 iL.
  Proof.
    move: 0 {-2 4 5}0 (leqnn 0); elim/gty_ind1: iG iL =>//.
    - by move=> iL n n0 _ _ /eqP-[<-].
    - by move=> v iL n n0 _ _ /eqP-[<-].
    - move=> G Ih iL n n0 n0_le_n /=.
      case Prj: project=>[iL'|]///guarded_match-[[d /andP-[EG n_d]]|[NV gG]].
      + move: EG Prj=>/eqP->[<-].
        case: ifP=>[/eqP-[F]|]; first by move=>/eqP-[<-].
        by move=>/(rwP negPf); rewrite -ltnNge => n_dn /eqP-[<-]/=.
      + case: (v_lty iL')=>[[v E]|l_not_var].
        * move: E Prj=>->/eqP-Prj; case: ifP; first by move=>_ /eqP-[<-].
          have {n0_le_n}n0_n: n0.+1 <= n.+1 by [].
          move: (Ih _ _ _ n0_n gG Prj)=>/= _ v_n /eqP-[<-]/=.
          by move: v_n; rewrite ltnNge=>->.
        * rewrite (@lty_not_var l_ty) // =>/eqP-[<-]/=.
          rewrite (@lty_not_var bool) //.
          by move: Prj=>/eqP/(Ih _ _ _ _ gG)-H; apply/H.
    - move=>p q Ks Ih iL n n0 n0n.
      rewrite project_msg=>/=/forallbP/forall_member-gKs.
      case PrjAll: prj_all => [KsL|]//; case: ifP=>// p_n_q.
      move: PrjAll=>/eqP/prjall_some2-PrjAll.
      case: ifP=>[p_r|p_n_r]; last case: ifP=>[q_r|q_n_r].
      + move=>/eqP-[<-]/=; apply/forallbP/forall_member=>K M.
        move: (PrjAll _ M)=> [G [MG /eqP-PrjG]].
        by apply/(lguarded_gt (leq0n n))/(Ih _ MG _ _ _ (leq0n n) (gKs _ MG)).
      + move=>/eqP-[<-]/=; apply/forallbP/forall_member=>K M.
        move: (PrjAll _ M)=> [G [MG /eqP-PrjG]].
        by apply/(lguarded_gt (leq0n n))/(Ih _ MG _ _ _ (leq0n n) (gKs _ MG)).
      + case: KsL PrjAll=>//=K KsL PrjAll M; move: (merge_some M)=><-.
        move: (PrjAll K (or_introl erefl))=>[G [MG /eqP-PrjG]].
        apply: (Ih _ MG _ _ _ (leq0n n)); last by apply/PrjG.
        by apply: gKs.
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

  Lemma project_depth d G r L :
    g_fidx d G == fset0 ->
    project d G r == Some L ->
    project d.+1 G r == Some L.
  Proof.
    elim/gty_ind1: G=>[|v|G Ih|p q Ks Ih]// in d L *.
    - move=>/=; case Prj: project=>[L'|//]; move: Prj=>/eqP-Prj Fv.
      move: (Ih _ _ Fv Prj) (gclosed_lclosed Fv Prj)=>/eqP->.
      case: (v_lty L')=>[[v'->]|/(@lty_not_var l_ty)-H]; last by rewrite ! H.
      move=>/=; case: ifP=>v_d; first by rewrite -cardfs_eq0 cardfs1.
      move: v_d; rewrite ltnNge=>/(rwP negPf); rewrite negbK=> H _.
      by rewrite H (leqW H).
    - rewrite !project_msg/==>/fsetUs_fset0/member_map-Fvs.
      case Prj: prj_all =>[KsL|//]; move: Prj=>/eqP-Prj.
      case: ifP=>// p_neq_q; suff: prj_all d.+1 Ks r == Some KsL by move=>/eqP->.
      elim: Ks =>[|K Ks IhKs]//= in KsL Ih Fvs Prj *.
      move: Prj; case Prj: project=>[Lk|//]; move: Prj=>/eqP-Prj.
      move: (Ih K (or_introl erefl) d Lk (Fvs K (or_introl erefl)) Prj)=>/eqP->.
      move: Ih Fvs=>/(_ _ (or_intror _))-Ih /(_ _ (or_intror _))-Fvs.
      move: Ih=> /IhKs/(_ Fvs); case: prj_all=>[KsL'|//] Ih /eqP-[E].
      by move: Ih=>/(_ KsL' (eq_refl _))/eqP->; move: E=><-.
  Qed.

  Lemma open_notvar n L L' :
    (forall v : nat, L != l_var v) ->
    (forall v : nat, l_open n L' L != l_var v).
  Proof. by case: L=>//v /(_ v)/eqP. Qed.

  (* Lemma project_open d r G1 G2 L1 L2 : *)
  (*   g_fidx d.+1 G1 == fset0 -> *)
  (*   g_fidx d G2 == fset0 -> *)
  (*   project d.+1 G1 r == Some L1 -> *)
  (*   project d G2 r == Some L2 -> *)
  (*   project d (g_open d G2 G1) r == Some (l_open d L2 L1). *)
  (* Proof. *)
  (*   elim/gty_ind1: G1 =>[|v1|G1 Ih/=|p q Ks1 Ih]// in d L1 *. *)
  (*   - by move=>_ _ /eqP-[<-]. *)
  (*   - by move=>_ _ /eqP-[<-]/=; case: ifP=>// _ /eqP. *)
  (*   - case Prj1: project=>[L1'|//]; move: Prj1=>/eqP-Prj1. *)
  (*     case Prj2: project=>[L2'|//]; move: Prj2=>/eqP-Prj2. *)
  (*     move=>FvG1 FvG2 /eqP-[EL1] /eqP-[EL2]. *)
  (*     move: (gclosed_lclosed FvG1 Prj1)=>FvL1. *)
  (*     move: EL2 Prj2 (gclosed_lclosed FvG2 Prj2)=>->{L2'}Prj2 FvL2. *)
  (*     move: Prj2=>/(project_depth FvG2)-Prj2. *)
  (*     move: FvG2 => /gfbvar_next/eqP-FvG2. *)
  (*     move: (Ih d.+1 _ FvG1 FvG2 Prj1 Prj2) => /eqP-Prj3. *)
  (*     rewrite Prj3/=; move: EL1=><-. *)
  (*     case: (v_lty L1')=>[[v' EL1']|H]. *)
  (*     + rewrite EL1' in Prj1 FvL1 Prj3 *; move=>{L1' EL1'}. *)
  (*       rewrite fun_if/=. *)
  (*       move: FvL1=>/=; case: ifP=>/=; first by rewrite -cardfs_eq0 cardfs1. *)
  (*       rewrite ltnNge=>/(rwP negPf); rewrite negbK. *)
  (*       case: ifP=>[/eqP->->|]. *)
  (*       admit. *)
  (*       admit. *)
  (*     + by rewrite (@lty_not_var l_ty _ _ _ H)/= *)
  (*                  (@lty_not_var l_ty _ _ _ (open_notvar _ _ H)). *)
  (* Admitted. *)

  Lemma project_var_parts d G v r :
    project d G r == Some (l_var v) -> r \notin participants G.
  Proof.
  Admitted.

  Lemma project_notin_end r G d :
    g_closed G ->
    r \notin participants G ->
    project d G r == Some l_end.
  Admitted.

  Lemma notin_nunroll r n G :
    r \notin participants G ->
    r \notin participants (n_unroll n G).
  Proof.
    elim: n G=>//= n Ih G H.
    by case: G H=>//= GT; rewrite /unroll=>/notin_part_g_open/Ih.
  Qed.

  Lemma project_open L G r
        (NV : forall v : nat, L != l_var v)
        (FV : g_fidx 1 G == fset0)
        (Prj : project 1 G r == Some L)
    : project 0 (unroll G) r == Some (l_open 0 (l_rec L) L).
  Admitted.

  (* TODO *)
  Lemma project_unroll m G r L :
    project 0 G r == Some L ->
    g_closed G ->
    exists n,
    project 0 (n_unroll m G) r = Some (lunroll n L).
  Proof.
    move=> Prj; elim: m => [|m Ih]//= in G L Prj *.
    - by (exists 0; apply/eqP).
    - move: Prj; case:(rec_gty G) => [[G'->]/=|/(@matchGrec g_ty)->/eqP->];
        last by exists 0.
      case Prj: project=>[L'|]//; move: Prj=>/eqP; case: (v_lty L')=>[[v->]|].
      * move=> Prj.
        have rG': r \notin participants G' by apply/project_var_parts/Prj.
        move=>/eqP-[<-]; rewrite /g_closed/= => Fv.
        move: (gclosed_lclosed Fv Prj) =>/=.
        case: ifP; first by rewrite -cardfs_eq0 cardfs1.
        rewrite ltnNge =>/(rwP negPf); rewrite negbK.
        case: v Prj=>// v _ _; move: rG'=>/notin_part_g_open/(notin_nunroll m)/=.
        have: g_closed (g_rec G') by [].
        move=>/gopen_closed/(g_closed_unroll m)/project_notin_end-H /H-{H}H.
        by exists 0; apply/eqP.
      * move=>NV; rewrite (@lty_not_var l_ty _ _ _ NV) => Prj /eqP-[<-] FV.
        move: (gopen_closed FV)=> cG; move: FV; rewrite /g_closed/= => FV.
        move: (project_open NV FV Prj)=>/Ih /(_ cG)-[n {Ih}Ih].
        by exists n.+1.
  Qed.

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
            project 0 iG FROM == Some iL ->
            GUnroll iG cG ->
            LUnroll iL cL ->
            r0 cG cL)
        (cG : forall x, member x CONT -> g_fidx 0 x.cnt == fset0)
        (gG : forall x, member x CONT -> guarded 0 x.cnt)
        (GU : @unroll_all (upaco2 g_unroll bot2) CONT CC)
        (LU : l_unroll_all (upaco2 l_unroll bot2) KsL C)
        (PRJ : prj_all 0 CONT FROM = Some KsL)
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
        (PRJ : prj_all 0 CONT r = Some Ks)
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
            project 0 iG r == Some iL ->
            GUnroll iG cG ->
            LUnroll iL cL ->
            r0 cG cL)
        (cL : l_closed L)
        (gL : lguarded 0 L)
        (cG : g_closed G)
        (gG : guarded 0 G)
        (nrG : forall G' : g_ty, G != g_rec G')
        (iPrj : project 0 G r = Some L)
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
    project 0 iG r == Some iL ->
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
    move=> cG cL [iG [cG' [ciG [giG [iGiL [GU LU]]]]]].
    move: (project_closed ciG iGiL) => ciL.
    move: (project_guarded giG iGiL) => giL.
    move : GU (unroll_guarded ciG giG)=>/(GUnroll_ind (rec_depth iG))=>GU nrG.
    move: (project_unroll (rec_depth iG) iGiL) => [U proj].
    move: LU =>/(LUnroll_ind U)=>LU.
    move: (g_guarded_nunroll (rec_depth iG) ciG giG)=>guiG.
    move: (g_closed_unroll (rec_depth iG) ciG)=>cuiG.
    move=> {ciG giG iGiL}.
    move: (l_guarded_nunroll U ciL giL)=>guiL.
    move: (l_closed_unroll U ciL)=>cuiL.
    move=>{ciL giL}.
    by apply/(project_nonrec CIH cuiL) =>//.
  Qed.
End CProject.

Print Assumptions ic_proj.
