From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco1 paco2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.
Require Import MPST.Global.
Require Import MPST.Local.

(*
  LG to All:
  comments about the new generic merge are marked
   NMC ,
  as in New Merge Comment
*)


Definition merge_all A (merge : A -> seq A -> option A) (K : seq A) :=
  match K with
  | h :: t => merge h t
  | _ => None
  end.

Section IProject_defs.

  Variables (merge : l_ty -> seq l_ty -> option l_ty).
  Notation merge_all := (merge_all merge).

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
                 match project K.2.2 r, proj_all Ks r with
                 | Some L, Some Ks => Some ((K.1, (K.2.1, L)) :: Ks)
                 | _, _ => None
                 end
               end
            ) Ks r with
      | Some Ks => if p == q then None
                   else if p == r then Some (l_msg l_send q Ks)
                        else if q == r then Some (l_msg l_recv p Ks)
                             else merge_all [seq K.2.2 | K <- Ks]
      | None => None
      end
    end.

  Fixpoint prj_all (Ks : seq (lbl * (mty * g_ty))) (r : role)
    : option (seq (lbl * (mty * l_ty))) :=
    match Ks with
    | [::] => Some [::]
    | K::Ks => match project K.2.2 r, prj_all Ks r with
               | Some L, Some Ks => Some ((K.1, (K.2.1, L)) :: Ks)
               | _, _ => None
               end
    end.

  Lemma project_msg p q Ks r
    : project (g_msg p q Ks) r =
      match prj_all Ks r with
      | Some Ks' => if p == q then None
                   else if p == r then Some (l_msg l_send q Ks')
                        else if q == r then Some (l_msg l_recv p Ks')
                             else merge_all [seq K.2.2 | K <- Ks']
      | None => None
      end.
  Proof. by []. Qed.

  Lemma prjall_some p Ks Ks' :
    prj_all Ks p == Some Ks' ->
    forall K, member K Ks ->
              exists L, member (K.1, (K.2.1, L)) Ks' /\
                        project K.2.2 p = Some L.
  Proof.
    elim: Ks => [|K Ks Ih]//= in Ks' *.
    case Kp: project => [Lp|//].
    case Ksp: prj_all => [LKs|//]; move: Ksp=>/eqP-Ksp.
    move=> /eqP-[Eq]; move: Eq Ih =><- Ih {Ks'} K0 [<-{K0}|].
    - by exists Lp; split=>//=; left.
    - by move=> /(Ih LKs Ksp K0)-[L [L_LKs PrjL]]; exists L; split=>//=; right.
  Qed.

  Lemma prjall_some2 p Ks Ks' :
    prj_all Ks p == Some Ks' ->
    forall K, member K Ks' ->
              exists G, member (K.1, (K.2.1, G)) Ks /\
                        project G p = Some K.2.2.
  Proof.
    elim: Ks' => [|K Ks' Ih]//= in Ks *.
    case: Ks=>// Kg Ks/=.
    case Kgp: project => [Lp|//].
    case Ksp: prj_all => [Ks''|//]; move: Ksp=>/eqP-Ksp.
    move=>/eqP-[<-{K} EqKs'']; move: EqKs'' Ksp=>->Ksp {Ks''}.
    move=> K [<-{K}|].
    - by exists (Kg.2.2) =>/=; split=>//; left; case: Kg {Kgp} => l [t G].
    - move=> M; move: (Ih Ks Ksp K M)=>[G [MG prjG]].
      by exists G; split=>//; right.
  Qed.

  Fixpoint project_all (parts : seq role) (g : g_ty)
    : option (seq (role * l_ty))
    := match parts with
       | [::] => Some [::]
       | p :: parts =>
         match project g p, project_all parts g with
         | Some l, Some e => Some ((p, l) :: e)
         | _, _ => None
         end
       end%fmap.

  Definition eproject (g : g_ty) : option (seq (role * l_ty)) :=
    if g_precond g
    then project_all (undup (participants g)) g
    else None.

  Lemma eproject_some g e :
    eproject g = Some e ->
    ~~ nilp (participants g) ->
    exists p l, project g p = Some l.
  Proof.
    rewrite /eproject; case:ifP=>// _; elim: (participants g)=>//= p ps Ih.
    case:ifP=>//.
    - by move=> p_in_ps /Ih-{}Ih _; apply: Ih; case: ps p_in_ps.
    - move=> _ /=.
      by case PRJ: project=>[L|]// _ _; exists p, L.
  Qed.

  Lemma fnd_not_part g e p :
    eproject g = Some e -> p \notin participants g -> find_cont e p = None.
  Proof.
    rewrite /eproject; case:ifP=>// _ PRJ; rewrite -mem_undup=>PARTS.
    elim: (undup (participants g)) PARTS e PRJ =>//=.
    - by move=> _ e [<-].
    - move => q l Ih.
      rewrite in_cons negb_or=>/andP-[pq] /Ih-{}Ih e.
      case PRJ: project=>[L|]//.
      case ALL: project_all=>[E|]//.
      by move=>[<-]; rewrite /=/extend eq_sym (negPf pq); apply/Ih.
  Qed.

  Lemma eproject_part (g : g_ty) (e : seq (role * l_ty)) :
    eproject g == Some e ->
    forall p,
      p \in participants g -> project g p = Some (odflt l_end (find_cont e p)).
  Proof.
    rewrite /eproject; case: ifP=>//WF; move: (participants g)=>p; elim:p e=>//=.
    move=> p ps Ih E/=; case: ifP.
    - by move=> p_in_ps /Ih-{}Ih p'; rewrite in_cons=>/orP-[/eqP->|]; apply/Ih.
    - move=>p_not_in/=.
      case PRJp: project=>[L|]//;case ALL: project_all=>[E'|]//.
      move=>/eqP-[<-] q; rewrite in_cons/= /extend eq_sym.
      by case:ifP=>[/eqP<-| _]//=; apply/Ih/eqP.
  Qed.

  Lemma prj_isend g
    : is_end g ->
      forall p, exists l, project g p = Some l /\ l_isend l.
  Proof.
    elim: g=>//.
    - by move=> _ p; exists l_end; split.
    - move=> G Ih /Ih-{}Ih p /=.
      move: (Ih p)=>[L][PRJ] END; rewrite PRJ/=.
      case: ifP=>//_; try by exists l_end.
      by exists (l_rec L); split.
  Qed.
End IProject_defs.

Section SimpleMerge.

  Fixpoint simple_merge  (oL : l_ty) (K : seq l_ty) :=
    match K with
    | [::] => Some oL
    | h::t => if h == oL then simple_merge oL t
              else None
    end.


(*NMC: Next lemma is specific to the old merge*)
  Lemma simple_merge_some (K : lbl * (mty * l_ty))
        (Ks : seq (lbl * (mty * l_ty))) L
    : simple_merge K.2.2 [seq K0.2.2 | K0 <- Ks] == Some L -> K.2.2 = L.
  Proof. by elim: Ks=>[/eqP-[]//|K' Ks Ih/=]; case:ifP. Qed.

(*NMC: specific to the old merge, namely the following lemmas connects
  the old merge for local types, which is now generic, and the merge for session types,
  which is still defined with equality of continuations*)

  Lemma fun_mergeall_old f (Ks : seq (lbl * (mty * l_ty))) X
    : injective f ->
      merge_all simple_merge [seq f x.2.2 | x <- Ks] == Some (f X) ->
      merge_all simple_merge [seq x.2.2 | x <- Ks] == Some X.
  Proof.
    case: Ks=>[//|K Ks/=] I; elim: Ks=>[|K' Ks]//=.
    - by move=>/eqP-[/I->].
    - by move=> Ih; case: ifP=>///eqP-[/I->]; rewrite eq_refl=>/Ih.
  Qed.

  Lemma mergeall_fun_old f (Ks : seq (lbl * (mty * l_ty))) X:
    merge_all simple_merge [seq x.2.2 | x <- Ks] == Some X
    -> merge_all simple_merge [seq f x.2.2 | x <- Ks] == Some (f X).
  Proof.
    case: Ks=>[//|K Ks/=]; elim: Ks=>[|K' Ks]//=.
    - by move=>/eqP-[->].
    - by move=> Ih; case: ifP=>///eqP-[->]; rewrite eq_refl=>/Ih.
  Qed.

  Lemma prjall_merge p Ks KsL L :
    prj_all simple_merge Ks p == Some KsL ->
    merge_all simple_merge [seq K0.2.2 | K0 <- KsL] == Some L ->
    forall K, member K Ks -> project simple_merge K.2.2 p == Some L.
  Proof.
    case: KsL=>//= Kl KsL; case: Ks=>//= Kg Ks.
    case Kg_p: project => [Lp | //]; case Ks_p: prj_all => [Ksp | //]/=.
    move=> Eq; move: Eq Ks_p => /eqP-[<-->] /eqP-Prj Mrg {Kl Ksp}.
    move:Mrg (simple_merge_some Mrg)=>/=Mrg Eq; move: Eq Mrg Kg_p=>->Mrg /eqP-Kg_p.
    move=> K [<-//|]; move: Prj Mrg K {Lp Kg_p Kg}.
    elim: Ks KsL=>//= Kg Ks Ih KsL.
    case Kg_p: project => [Lp | //]; case Ks_p: prj_all => [Ksp | //]/=.
    move=> Eq; move: Eq Ih Ks_p Kg_p=>/eqP-[<-]//= Ih /eqP-Prj.
    case: ifP=>[/eqP-> {Lp}|//] /eqP-Kg_p Mrg K [<-//|].
    by move: Prj=>/Ih/(_ Mrg K).
  Qed.

  Lemma notin_flatten (A: eqType) (p : A) Ks :
    (forall K, member K Ks -> p \notin K) ->
    p \notin flatten Ks.
  Proof.
    elim: Ks=>//=K Ks Ih H; rewrite mem_cat negb_or (H _ (or_introl erefl)) Ih//.
    by move=> K0 M; apply/H; right.
  Qed.

  Lemma flatten_notin (A: eqType) (p : A) Ks :
    p \notin flatten Ks ->
    (forall K, member K Ks -> p \notin K).
  Proof.
    elim: Ks=>//=K Ks Ih; rewrite mem_cat negb_or=>/andP-[pK pKs] K' [<-//|].
    by move: K'; apply/Ih.
  Qed.

  Lemma notin_parts_project Lp p G
       (Ep : project simple_merge G p = Some Lp)
       (NIN : p \notin participants G)
    : p \notin partsL Lp.
  Proof.
  elim: G=>[|v|G Ih|q r Ks Ih] in Lp NIN Ep *; move: Ep=>[].
  - by move<-.
  - by move<-.
  - move=>/=; case Ep: project=>[Lp'|//]; case: ifP=>//; first by move=>_[<-].
      by move=> _ [<-]/=; apply/Ih.
  - rewrite project_msg; case Ep:prj_all=>[Ks'|//]; case:ifP=>//Npq.
    move: NIN=>/=; rewrite !in_cons !negb_or=>/andP-[N1 /andP-[N2 NIN]].
    rewrite eq_sym (negPf N1) eq_sym (negPf N2) => M.
    have [K MK]: (exists K, member K Ks).
    + case: Ks Ep {Ih NIN}=>[[E]|K Ks _]//=; last (by exists K; left).
      by move: E M=><-.
    + move: Ep M=>/eqP-Ep /eqP-M; move: (prjall_merge Ep M)=>H.
      move: NIN=>/flatten_notin/member_map-H' {Ep M N1 N2 Npq Ks'}.
         by apply/(Ih _ MK); first (by apply/H'); apply/eqP/H.
   Qed.

  Lemma l_binds_notin Lp p G
        (Ep : project simple_merge G p = Some Lp)
        (BLp : l_binds 0 Lp)
    : p \notin participants G.
  Proof.
    elim: G 0 =>[|v|G Ih|q r Ks Ih] n//= in Lp BLp Ep *.
    - move: Ep Ih; case Prj: project=>[L|//]; move: Prj=>/eqP-Prj; case: ifP.
      + move=> B [E]; move: E BLp=><- _.
        by move=>/(_ _ _ B erefl).
      + by move=>_ [E]; move: E BLp=><-/= BLp /(_ _ _ BLp erefl).
    - move: Ep; move: (project_msg simple_merge q r Ks p)=>/=->.
      case Prj: prj_all=>[Ks'|//]; case: ifP=>// Eqr.
      case: ifP=>Eqp; first by move=> [E]; move: E BLp=><-.
      case: ifP=>Erp; first by move=> [E]; move: E BLp=><-.
      rewrite !in_cons eq_sym Eqp eq_sym Erp /==>M.
      apply/notin_flatten/member_map=> K Mm; apply/(Ih _ Mm _ _ BLp).
      by move: Prj M=>/eqP-Prj /eqP-M; move: (prjall_merge Prj M)=>/(_ _ Mm)/eqP.
  Qed.

  Lemma project_var_notin p G v L :
    (L == l_end) || (L == l_var v) ->
    project simple_merge G p == Some L ->
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
    project simple_merge (g_msg r s Ks) p == Some (l_var n) ->
    r != p /\ s != p /\ r != s /\
    (forall K, member K Ks -> project simple_merge K.2.2 p == Some (l_var n)).
  Proof.
    rewrite project_msg; case Ksp: prj_all => [Ks'|//]; move: Ksp=>/eqP.
    do ! case: ifP=>//; move=>s_ne_p r_ne_p r_ne_s.
    by move=>/prjall_merge-H /H.
  Qed.

  Lemma proj_var_eq G p q v v':
    project simple_merge G p == Some (l_var v) ->
    project simple_merge G q == Some (l_var v') ->
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
      move=>/simple_merge_some-Ep /simple_merge_some-Eq; move: Ep Eq Pp Pq=>/=->->.
      by apply: Ih.
  Qed.

  Lemma prjall_merge_cons Ks p KsL L :
    prj_all simple_merge Ks p = Some KsL ->
    merge_all simple_merge [seq K.2.2 | K <- KsL] = Some L ->
    exists K, member K Ks.
  Proof.
    case: Ks=>//=; first by move=>[<-].
    move=> K Ks; case Prj:project=>[L'|//]; case PrjA:prj_all=>[KL'|//].
    by move=>_ _; exists K; left.
  Qed.

  Lemma project_binds_eq p q G Lp Lq n m :
    project simple_merge G p = Some Lp ->
    project simple_merge G q = Some Lq ->
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

  Lemma gclosed_lclosed d G r L :
    g_fidx d G == [::] ->
    project simple_merge G r == Some L ->
    l_fidx d L == [::].
  Proof.
    elim: G =>[|v|G Ih|p q Ks Ih] in d L *.
    - by move=> _ /eqP-[<-].
    - move=> /=; case: ifP=>//.
      by move=> H _ /eqP-[<-]/=; rewrite H.
    - move: Ih=>/=; case Eq: project =>[Lr|//]; move: Eq=>/eqP-Eq.
      move=> /(_ d.+1 Lr)-Ih /Ih/(_ (eq_refl _))-H.
      case: ifP=>//; first by move=> _ /eqP-[<-].
      by move=>B /eqP-[<-]/=; apply/H.
    - rewrite project_msg=>H1.
      case Eq: prj_all => [Ks'|//]; case: ifP=>[//|p_neq_q]/=.
      move: Eq=>/eqP-Eq.
      case: ifP=>[p_eq_r /eqP-[<-]/=|p_neq_r].
      * rewrite !flatten_eq_nil !member_map in H1 * => H1.
        move=> K M; move: (prjall_some2 Eq M)=>[G [M' /eqP-PrjG]].
        by apply: (Ih _ M'); first (by rewrite H1 // H2); apply: PrjG.
      * case: ifP=>[q_eq_r /eqP-[<-]|q_neq_r /eqP].
        + rewrite !flatten_eq_nil !member_map in H1 *=> H1 K M.
          move: (prjall_some2 Eq M) =>[G [M' /eqP-PrjG]].
          by apply: (Ih _ M'); first (by rewrite H1 // H2); apply: PrjG.
        + case: Ks' Eq=>// Kl Ks' Eq /eqP/simple_merge_some<- /=.
          case: Ks Eq Ih H1=>//= Kg Ks.
          case Eqg: project =>[Lk|//].
          case EqKs: prj_all =>[Ks''|//].
          rewrite !cat_eq_nil => /eqP-[<- H2] Ih [H3 H4].
          by apply: (Ih  Kg)=>//=; [left=>//|apply/eqP]; apply: Eqg.
  Qed.

  Lemma prjall_open r n g l Ks Ks' :
    (forall p : lbl * (mty * g_ty),
      member p Ks ->
      forall s : lty_eqType,
        project simple_merge p.2.2 r == Some s ->
        project simple_merge (g_open n g p.2.2) r = Some (l_open n l s)) ->
    prj_all simple_merge Ks r = Some Ks' ->
    prj_all simple_merge [seq (K.1, (K.2.1, g_open n g K.2.2)) | K <- Ks] r
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
    project simple_merge iG r == Some iL ->
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
    project simple_merge G r == Some (l_var v) -> r \notin participants G.
  Proof. by apply/project_var_notin/orP/or_intror/eq_refl. Qed.


  Lemma prj_open_binds L1 L2 G r :
    project simple_merge G r = Some L1 ->
    l_binds 0 L1 ->
    project simple_merge (g_open 0 (g_rec G) G) r = Some L2 ->
    l_isend L2.
  Proof.
    move=>P1 B1; have []: project simple_merge G r = Some L1 /\ l_binds 0 L1 by split.
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

  Lemma project_g_open_comm G1 G2 r L1 L2 k:
    g_closed G1 ->
    project simple_merge G1 r = Some L1 -> project simple_merge G2 r = Some L2 ->
    project simple_merge (g_open k G1 G2) r = Some (l_open k L1 L2).
  Proof.
  elim: G2 G1 k L1 L2.
  + by move=> G1 k L1 L2 gclo eq1 => //=; move=> [eq2]; rewrite -eq2 //=.
  + move=> VAR G1 k L1 L2 gclo eq1 => //=; move=> [eq2]; rewrite -eq2 //=.
    case: ifP=>//; move:eq1=>/eqP-eq1.
    by move: (gclosed_lclosed gclo eq1)=>/lshift_closed-> _; apply/eqP.
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
          by rewrite <-map_comp; rewrite (rwP eqP); apply mergeall_fun_old.
        + by move=> p mem loc; rewrite <-(rwP eqP); move=> prS; apply IH; rewrite //=.
        + by [].
  Qed.

  Lemma project_open L G r
    : l_binds 0 L == false -> g_closed (g_rec G) ->
  project simple_merge G r = Some L -> project simple_merge (unroll G) r = Some (l_open 0 (l_rec L) L).
  Proof.
  move=> nlb cl prS.
  have: project simple_merge (g_rec G) r = Some (l_rec L).
    move: prS; rewrite //=; case Prj: project=>[LT| //=].
    by move=> eq; move: eq Prj nlb=>[<-] Prj; case: ifP=>//=.
  move=> prrecS; apply project_g_open_comm; rewrite //=.
  Qed.

  Lemma project_open_end_strong L G1 G r k:
    project simple_merge G r = Some L -> project simple_merge G1 r = Some (l_end)->
    project simple_merge (g_open k G1 G) r = Some (l_open k l_end L).
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
          by rewrite <-map_comp; rewrite (rwP eqP); apply mergeall_fun_old.
        + by move=> p mem loc; rewrite <-(rwP eqP); move=> prS; apply Ih; rewrite //=.
        + by [].
  Qed.

  Lemma project_open_end L G r : l_binds 0 L -> project simple_merge G r = Some L
    -> project simple_merge (unroll G) r = Some (l_open 0 l_end L).
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
    project simple_merge G r = Some L ->
    l_isend L ->
    exists L', project simple_merge (n_unroll n G) r = Some L' /\ l_isend L'.
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
    project simple_merge G r = Some L ->
    (* g_closed G -> *)
    exists n1 n2 L',
    project simple_merge (n_unroll m G) r = Some L' /\ lunroll n1 L = lunroll n2 L'.
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
                        else all (depth_part m p) [seq K.2.2 | K <- Ks ]
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
    project simple_merge G p == Some L ->
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
    - rewrite -/(prj_all _ _).
      case PRJ: prj_all=>[Ks|]//; case: ifP=>// FT.
      case: ifP=>[|].
      + by move=>/eqP<-/eqP-[<-]; split=>// _; exists 1; rewrite /=eq_refl.
      case: ifP=>[|].
      + by move=>/eqP<- _/eqP-[<-];split=>//_; exists 1; rewrite /=eq_refl orbC.
      + rewrite eq_sym=> pT; rewrite eq_sym =>pF MRG; split.
        * move=> VAR; move: Ih=>/(_ _ _ L); rewrite VAR=>Ih.
          move: PRJ=>/eqP-PRJ; move: (prjall_merge PRJ MRG)=>{}PRJ.
          have {}Ih: forall K,
              member K C -> exists n : nat, depth_part n p K.2.2
                by move=> K M; move: PRJ Ih=>/(_ _ M)-PRJ /(_ _ M PRJ)-<-.
          move => {PRJ VAR MRG Ks L}.
          suff: exists n, forall K, member K C -> depth_part n p K.2.2
                by move=>[n H]; exists n.+1=>/=; rewrite pF pT/=;
                     apply/forallbP/forall_member/member_map.
          move=> {FT pF pT F T}; elim: C=>[|K C IhC] in Ih *; first by (exists 0).
          move: (Ih K (or_introl erefl))=>[n DK].
          move: Ih=>/(_ _ (or_intror _))=>/IhC-[m] H.
          exists (maxn n m)=> K' [<-|/H-{}DK]; apply/(depth_next _ DK).
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
    project simple_merge G p == Some L ->
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
    project simple_merge G p == Some L -> l_binds k L -> depth_part n p G = false.
  Proof.
    move=>/project_depth'=>[][_ /(_ (ex_intro _ n _))-H B]; move: H.
    rewrite negb_or andbC (lbinds_isvar B)=>/=; case: depth_part=>//.
    by move=>/(_ is_true_true).
  Qed.

  Lemma prj_all_find C p Ks l Ty G :
    prj_all simple_merge C p = Some Ks -> find_cont C l = Some (Ty, G) ->
    exists L, member (l, (Ty, L)) Ks /\ project simple_merge G p = Some L.
  Proof.
    elim: C Ks=>// [][l'][Ty']G' Ks Ih Ks' /=; rewrite /extend.
    case PRJ: project=>[L|]//; case PRJA: prj_all=>[KsL|]//= [<-]/=.
    case: ifP=>[/eqP->|].
    - by move=>[-><-]; exists L; split=>//; left.
    - by move=> ll' /(Ih _ PRJA)-[L' [M PRJ']]; exists L'; split=>//; right.
  Qed.

  Lemma project_parts' p G L :
    project simple_merge G p == Some L ->
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
    - move=> q r Ks Ih L; rewrite -/(prj_all _ _); case PRJ: prj_all=>[KsL|]//.
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
    project simple_merge G p == Some L ->
    l_isend L || l_isvar L ->
    p \notin participants G.
  Proof.
    elim: G L=>//.
    - move=> G Ih L /=; case PRJ: project=>[L'|//]; move: PRJ =>/eqP-PRJ.
      case: ifP=>//.
      + move=> /lbinds_isvar-L'var _ _; apply/(Ih L')=>//.
        by rewrite L'var orbT.
      + by move=> _ /eqP-[<-]/=; apply/Ih.
    - move=>q r Ks Ih L/=; rewrite -/(prj_all _ _).
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
    project simple_merge G p == Some L ->
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
    project simple_merge G p == Some L ->
    ~~ l_isend L <->
    p \in participants G.
  Proof.
    move=> cG pG; split.
    - by move=> /negPf; apply/contraFT=>/(project_parts cG pG).
    - by move=>P; apply/negPf; move:P; apply/contraTF=>/(project_parts cG pG).
  Qed.

  Lemma prjall_dom cG cL p :
    prj_all simple_merge cG p = Some cL -> same_dom (find_cont cG) (find_cont cL).
  Proof.
    elim: cG cL=>//=.
    - by move=>cL [<-]/= l Ty; split=>[][G].
    - move=> [l P] Ks Ih cL; case: project=>[L|]//.
      case ALL: prj_all=>[CL|]//[<-] l' Ty'/=; move: ALL=>/Ih-{}Ih.
      split=>[][G]; rewrite /extend; case: ifP=>_.
      + by move=> [->]/=; exists L.
      + by move=>/(dom Ih).
      + by move=>[<-] _; exists P.2; case: P.
      + by move=>/(dom' Ih).
  Qed.

  Lemma prjall_fnd cG cL p G Ty L l :
    prj_all simple_merge cG p = Some cL ->
    find_cont cG l = Some (Ty, G) -> find_cont cL l = Some (Ty, L) ->
    project simple_merge G p = Some L.
  Proof.
    elim: cG cL=>//=.
    - move=> [l' [Ty' G']] Ks Ih cL; case PRJ: project=>[L'|]//.
      case ALL: prj_all=>[cL'|]// [<-] {cL}.
      rewrite /extend; case: ifP.
      + by move=>/eqP-> [<-<-]/=; rewrite /extend eq_refl=>[][<-].
      + by move=>NEQ FND1 /=; rewrite /extend NEQ; apply/Ih.
  Qed.

  Lemma prj_all_find_strong  C p Ks l Ty G :
    prj_all simple_merge C p = Some Ks -> find_cont C l = Some (Ty, G) ->
    exists L,
      member (l, (Ty, L)) Ks /\
      project simple_merge G p = Some L /\
      find_cont Ks l = Some (Ty, L).
  Proof.
    elim: C Ks=>// [][l'][Ty']G' Ks Ih Ks' /=; rewrite /extend.
    case PRJ: project=>[L|]//; case PRJA: prj_all=>[KsL|]//= [<-]/=.
    case: ifP=>[/eqP->|].
    - move=>[-><-]; exists L; split=>//; [by left|split; [by []|]].
      by rewrite /extend; case: ifP=>//; rewrite eq_refl.
    - move=> ll' /(Ih _ PRJA)-[L' [M [PRJ' FND']]]; exists L'.
      split=>//; [by right|split; [by []|]].
      by rewrite /extend; case: ifP; [rewrite ll'| move=> _].
  Qed.

  Lemma simple_merge_equal L Ks :
    simple_merge L [seq K.2.2 | K <- Ks] = Some L ->
    forall (K : (lbl * (mty  * l_ty))), member K Ks -> K.2.2 = L.
  Proof.
    elim: Ks=>//= K Ks Ih; case: ifP=>//.
    by move=>/eqP-Kl /Ih-{}Ih K0 [<-|/Ih].
  Qed.

  Lemma proj_lclosed G p L : g_closed G -> project simple_merge G p == Some L -> l_closed L.
  Proof.
    rewrite /g_closed/l_closed; move: 0.
    elim: G => [| v | {}G Ih | F T C Ih]/= in L *; rewrite -/prj_all.
    - by move=>n _ /eqP-[<-].
    - by move=>n H /eqP-[<-]/=.
    - move=>n /Ih-{}Ih; case PRJ: project=>[L'|//].
      case: ifP;[move=>_/eqP-[<-]//|move=>_ /eqP-[<-]/=].
      by apply/Ih/eqP.
    - move=>n /flatten_eq_nil/member_map-cG; rewrite -/(prj_all _ _).
      case ALL: prj_all=>[CL|//]; move: ALL=>/eqP-ALL; do ! case: ifP=>// _.
      + move=>/eqP-[<-]/=; apply/flatten_eq_nil/member_map=> K M.
        move: (prjall_some2 ALL M)=>[G][MG]/eqP-PRJ.
        by apply/(Ih _ MG _ _ (cG _ MG) PRJ).
      + move=>/eqP-[<-]/=; apply/flatten_eq_nil/member_map=> K M.
        move: (prjall_some2 ALL M)=>[G][MG]/eqP-PRJ.
        by apply/(Ih _ MG _ _ (cG _ MG) PRJ).
      + move=>MRG; move: (prjall_merge ALL MRG)=>PRJ.
        move: ALL MRG=>/eqP-ALL /eqP-MRG; move: (prjall_merge_cons ALL MRG).
        by move=>[K]M; apply/(Ih _ M _ _ (cG _ M) (PRJ _ M)).
  Qed.

  Lemma proj_lne G p L :
    non_empty_cont G -> project simple_merge G p == Some L -> l_non_empty_cont L.
  Proof.
    rewrite /g_closed/l_closed.
    elim: G => [| v | {}G Ih | F T C Ih]/= in L *; rewrite -/prj_all.
    - by move=>_ /eqP-[<-].
    - by move=>H /eqP-[<-]/=.
    - move=>/Ih-{}Ih; case PRJ: project=>[L'|//].
      case: ifP;[move=>_/eqP-[<-]//|move=>_ /eqP-[<-]/=].
      by apply/Ih/eqP.
    - move=>/andP-[NE]; rewrite -/(prj_all _ _).
      case ALL: prj_all=>[CL|//]; move: (prjall_dom ALL).
      move=>/samedom_nilp/contra/(_ NE)=>nilCL; move: ALL=>/eqP-ALL.
      move=>/forallbP/forall_member/member_map=>{}NE.
      do ! case: ifP=>// _.
      + move=>/eqP-[<-]/=; rewrite nilCL/=.
        apply/forallbP/forall_member/member_map=> K M.
        move: (prjall_some2 ALL M)=>[G][MG]/eqP-PRJ.
        by apply (Ih _ MG _ (NE _ MG) PRJ).
      + move=>/eqP-[<-]/=; rewrite nilCL/=.
        apply/forallbP/forall_member/member_map=> K M.
        move: (prjall_some2 ALL M)=>[G][MG]/eqP-PRJ.
        by apply (Ih _ MG _ (NE _ MG) PRJ).
      + move=>MRG; move: (prjall_merge ALL MRG)=>PRJ.
        move: ALL MRG=>/eqP-ALL /eqP-MRG; move: (prjall_merge_cons ALL MRG).
        by move=>[K]M; apply/(Ih _ M _ (NE _ M) (PRJ _ M)).
  Qed.

End SimpleMerge.
