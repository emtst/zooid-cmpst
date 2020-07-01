From mathcomp Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco2.

Require Import MPST.Actions.
Require Import MPST.AtomSets.
Require Import MPST.Forall.
Require Import MPST.Global.
Require Import MPST.Projection.
Require Import MPST.Local.
Require Import MPST.TraceEquiv.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Inductive Proc :=
| Finish

| Jump (v : nat)
| Loop of Proc

| Recv (p : role) of Alts
| Send (p : role) T (l : lbl) : coq_ty T -> Proc -> Proc

with Alts :=
| A_sing {T} (l : lbl) : (coq_ty T -> Proc) -> Alts
| A_cons {T} (l : lbl) : (coq_ty T -> Proc) -> Alts -> Alts
.

Fixpoint in_alts l T (alt : coq_ty T -> Proc) (alts : Alts) : Prop
  := match alts with
     | A_sing T' l' alt' =>
       match @eqP _ T T' with
       | ReflectT EQ =>
         match EQ with
         | erefl => fun alt' => l = l' /\ alt = alt'
         end alt'
       | ReflectF _ => False
       end
     | A_cons T' l' alt' alts =>
       match @eqP _ T T' with
       | ReflectT EQ =>
         match EQ with
         | erefl => fun alt' => l = l' /\ alt = alt' \/ in_alts l alt alts
         end alt'
       | ReflectF _ => in_alts l alt alts
       end
     end.

Fixpoint p_shift (n d : nat) (P : Proc) : Proc :=
  match P with
  | Finish => Finish
  | Jump v => if v >= d then Jump (n + v) else Jump v
  | Loop P => Loop (p_shift n d.+1 P)
  | Recv p alts => Recv p (alt_shift n d alts)
  | Send p _ l t P => Send p l t (p_shift n d P)
  end
with alt_shift (n d : nat) (alts : Alts) : Alts :=
       match alts with
       | A_sing _ l dproc =>
         A_sing l (fun t => p_shift n d (dproc t))
       | A_cons _ l dproc alts' =>
         A_cons l (fun t => p_shift n d (dproc t)) (alt_shift n d alts')
       end
  .

(* open variable d, with process P2 in process P1 *)
Fixpoint p_open (d : nat) (P2 P1 : Proc) : Proc :=
  match P1 with
  | Finish => Finish
  | Jump v => if v == d then p_shift d 0 P2 else P1
  | Loop P => Loop (p_open d.+1 P2 P)
  | Recv p alts => Recv p (alt_open d P2 alts)
  | Send p _ l t P => Send p l t (p_open d P2 P)
  end
with alt_open (d : nat) (P2 : Proc) (alts : Alts) : Alts :=
       match alts with
       | A_sing _ l dproc =>
         A_sing l (fun t => p_open d P2 (dproc t))
       | A_cons _ l dproc alts' =>
         A_cons l (fun t => p_open d P2 (dproc t)) (alt_open d P2 alts')
       end
  .


(* counts the top level nestedness of recursion in a process. To count
   how many unrolls to expose a top level action *)
Fixpoint prec_depth P :=
  match P with
  | Loop P => (prec_depth P).+1
  | _ => 0
  end.

(* Unroll d times the toplevel recursion *)
Fixpoint punroll d P :=
  match d with
  | 0 => P
  | d.+1 =>
    match P with
    | Loop P' => punroll d (p_open 0 P P')
    | _ => P
    end
  end.
(* the correctness conditions is that punroll (prec_depth P) P is
   either Finish or Send or Recv *)

Fixpoint find_alt alts l :=
  match alts with
  | A_sing T l' rK
    => if l == l' then Some (existT (fun=>_) T rK) else None
  | A_cons T l' rK alts
    => if l == l' then Some (existT (fun=>_) T rK)
       else find_alt alts l
  end.


Definition find_alt_ty alts l
  := match find_alt alts l with
     | Some K => Some (projT1 K, tt)
     | None => None
     end.

Inductive of_lt : Proc -> l_ty -> Prop :=
| t_Finish : of_lt Finish l_end

| t_Jump (v : nat) : of_lt (Jump v) (l_var v)
| t_Loop L P : of_lt P L -> of_lt (Loop P) (l_rec L)

| t_Recv a (p : role) (alts : Alts) :
    same_dom (find_alt_ty alts) (find_cont a) ->
    (forall l Ty rK L,
        find_alt alts l = Some (existT _ Ty rK) ->
        find_cont a l = Some (Ty, L) ->
        forall pl,
          of_lt (rK pl) L) ->
    of_lt (Recv p alts) (l_msg l_recv p a)

| t_Send (p : role) L a T (l : lbl)
  (payload : coq_ty T) (K : Proc) :
    of_lt K L ->
    find_cont a l == Some (T, L) ->
    of_lt (Send p l payload K) (l_msg l_send p a)
.

Section OperationalSemantics.

  (* runtime action *)
  Inductive rt_act :=
  | mk_rt_act (a : l_act) (p : role) (q : role) (l : lbl) (T : mty) (t :  coq_ty T).

  Definition erase_act a :=
  let: mk_rt_act a p q l T _ := a in mk_act a p q l T.


  Definition process_alt
             (T' : mty) (l' : lbl) (dproc : coq_ty T' -> Proc) (A : rt_act) (f: rt_act -> option Proc) : option Proc:=
    let: mk_rt_act a p q l T t := A in
    if (l == l') then
      match @eqP _ T T' with
      | ReflectT HTT' =>
        match esym HTT' with
        | erefl => fun t => Some (dproc t)
        end t
      | ReflectF _ => None
      end
    else f A
  .

  Definition do_step_proc (P : Proc) (A : rt_act) : option Proc :=
    let: (mk_rt_act a p q l T t) := A in
    (* we unroll the process to expose actions *)
    match punroll (prec_depth P) P with
    | Send q' T' l' t' K =>
      if (a == l_send) && (q == q') && (l == l') (* && (t == t') this requires the work below *)
      then match @eqP _ T T' with
           | ReflectT HTT' => (* if the types are equal *)
             match esym HTT' with
             | erefl =>
               (* we refine T = T' and compare the payloads *)
               fun t=> if t == t' then Some K else None
             end t
           | ReflectF _ => None
           end
      else None
    | Recv q' alts =>
      if (a == l_recv) && (q == q') then
        match find_alt alts l with
        | None => None
        | Some (existT T' rK) =>
          match @eqP _ T T' with
          | ReflectT HTT' =>
            match esym HTT' with
            | erefl => fun t => Some (rK t)
            end t
          | ReflectF _ => None
          end
        end
      else
        None
    | Loop P => None (* this cannot happen as we unrolled the process *)
    | Jump _ => None (* open process, it can't step *)
    | Finish => None
    end
  .

  Definition run_step_proc P A : Proc := odflt P (do_step_proc P A).

  Lemma same_red_depth P L:
    of_lt P L -> prec_depth P = lrec_depth L.
  Proof.
    elim=>// L0 P0 H0 Eq.
    rewrite/prec_depth/lrec_depth=>//=.
    by rewrite-/prec_depth-/lrec_depth Eq.
  Qed.

  Lemma find_alt_ty_open n P alts
    : same_dom (find_alt_ty (alt_open n P alts)) (find_alt_ty alts).
  Proof.
    move=> l Ty; split=>[][][] H; exists tt; move: H; rewrite /find_alt_ty.
    - by elim: alts=>[T l0 rK|T l0 rK a]//=; case: ifP.
    - by elim: alts=>[T l0 rK|T l0 rK a]//=; case: ifP.
  Qed.

  Lemma find_alt_ty_shift n d alts
    : same_dom (find_alt_ty (alt_shift n d alts)) (find_alt_ty alts).
  Proof.
    move=> l Ty; split=>[][][] H; exists tt; move: H; rewrite /find_alt_ty.
    - by elim: alts=>[T l0 rK|T l0 rK a]//=; case: ifP.
    - by elim: alts=>[T l0 rK|T l0 rK a]//=; case: ifP.
  Qed.

  Lemma same_dom_map T T' (f : T -> T') (Ks : seq (lbl * (mty * T)))
    : same_dom (find_cont Ks) (find_cont [seq (K.1, (K.2.1, f K.2.2)) | K <- Ks]).
  Proof.
    elim: Ks=>[|[l [Ty t]] Ks Ih]//=; rewrite /extend; first by split=>[][]x//=.
    move=>l' Ty'; split=>[][]x; case: ifP=>// _ [EQ];
      try rewrite EQ; try (by exists t); try (by exists (f t)).
    - by move: (dom Ih EQ).
    - by move: (dom' Ih EQ).
  Qed.

  Lemma find_alt_open n P alts l Ty rK
    : find_alt (alt_open n P alts) l = Some (existT (fun=>_) Ty rK) ->
      exists rK',
        find_alt alts l = Some (existT (fun=>_) Ty rK') /\
        rK = (fun l => p_open n P (rK' l)).
  Proof.
    elim: alts=>[T l0 rK''|T l0 rK'' alts Ih]/=; case:ifP=>// _.
    - move=> [H]; move: H rK''=>-> rK'' H.
      rewrite -(Eqdep_dec.inj_pair2_eq_dec _ _ _ _ _ _ H);
        last by move=>x y; apply/(decP eqP).
      by exists rK''; split.
    - move=> [H]; move: H rK''=>-> rK'' H.
      rewrite -(Eqdep_dec.inj_pair2_eq_dec _ _ _ _ _ _ H);
        last by move=>x y; apply/(decP eqP).
      by exists rK''; split.
  Qed.

  Lemma find_alt_shift n d alts l Ty rK
    : find_alt (alt_shift n d alts) l = Some (existT (fun=>_) Ty rK) ->
      exists rK',
        find_alt alts l = Some (existT (fun=>_) Ty rK') /\
        rK = (fun l => p_shift n d (rK' l)).
  Proof.
    elim: alts=>[T l0 rK''|T l0 rK'' alts Ih]/=; case:ifP=>// _.
    - move=> [H]; move: H rK''=>-> rK'' H.
      rewrite -(Eqdep_dec.inj_pair2_eq_dec _ _ _ _ _ _ H);
        last by move=>x y; apply/(decP eqP).
      by exists rK''; split.
    - move=> [H]; move: H rK''=>-> rK'' H.
      rewrite -(Eqdep_dec.inj_pair2_eq_dec _ _ _ _ _ _ H);
        last by move=>x y; apply/(decP eqP).
      by exists rK''; split.
  Qed.

  Lemma find_cont_map (L : l_ty) (Ks : seq (lbl * (mty * l_ty))) Ty l f :
    find_cont [seq (K.1, (K.2.1, f K.2.2)) | K <- Ks] l = Some (Ty, L) ->
    exists L0,
      find_cont Ks l = Some (Ty, L0) /\ L = f L0.
  Proof.
    elim: Ks=>//= [][l'][Ty'] L0 Ks Ih.
    by rewrite /extend/=; case:ifP=>// _ [-><-]; exists L0.
  Qed.

  Lemma shift_preserves_type n d P L :
    of_lt P L ->
    of_lt (p_shift d n P) (l_shift d n L).
  Proof.
    move=>H; elim: H=>
    [
    | v
    | {}L {}P  H Ih
    | K p alts DOM _ Ih
    | p {}L K Ty l payload {}P H0 Ih fnd
    ]//= in n *; try by (try (case: ifP); constructor).
    - constructor;
        first by apply/(same_dom_trans _ (same_dom_map _ _))
                      /(same_dom_trans _ DOM)/find_alt_ty_shift.
      move=>l Ty rK L0 /find_alt_shift-[rK'] [EQ0->] /find_cont_map-[L1][EQ1->].
      by move=> pl; apply/(Ih _ _ _ _ EQ0 EQ1).
    - apply/t_Send; first by apply/Ih.
      elim: K fnd=>//= [][k v] t {}Ih; rewrite /extend/=.
      by case: ifP=>// _ /eqP-[->]/=.
  Qed.

  (* TODO: can we generalise: of_lt (f P) (f' L) relate f f' in some way? *)
  Lemma open_preserves_type P P' L L' :
    of_lt P' L' -> of_lt P L -> of_lt (p_open 0 P' P) (l_open 0 L' L).
  Proof.
    move: 0 => n H H'; elim: H' n =>
    [
    | v
    | {}L {}P Ih
    | K p alts DOM _ Ih
    | p {}L K Ty l payload {}P H0 Ih fnd
    ]/= n; try by (constructor).
    - case: (ifP (v == n))=>_; try by constructor.
      by apply/shift_preserves_type.
    - apply/t_Recv;
        first by apply/(same_dom_trans _ (same_dom_map _ _))
                      /(same_dom_trans _ DOM)/find_alt_ty_open.
      move=> l Ty rK L0 /find_alt_open-[rK'] [EQ0->] /find_cont_map-[L1][EQ1->].
      by move=> pl; apply/(Ih _ _ _ _ EQ0 EQ1).
    - apply/t_Send; first by apply/Ih.
      elim: K fnd=>//= [][k v] t {}Ih; rewrite /extend/=.
      by case: ifP=>// _ /eqP-[->]/=.
  Qed.

  Lemma unroll_preserves_type P L n:
    of_lt P L -> of_lt (punroll n P) (lunroll n L).
  Proof.
    elim: n P L=>// n Ih P L; case=>//=; try by constructor.
    {
      move=>{}L {}P HP; apply: Ih.
      have HP' : of_lt (Loop P) (l_rec L) by constructor.
      by apply: open_preserves_type.
    }
    {
      by move=>p {}L a T l payload K HL Hfind ; apply: (t_Send _ _ HL).
    }
  Qed.

  Theorem preservation P Ps A L:
    of_lt P L ->
    do_step_proc P A = Some Ps ->
    of_lt Ps (run_act_l_ty L (erase_act A)).
  Proof.

    rewrite/run_step_proc/run_act_l_ty/do_step_proc/do_act_l_ty.
    case A => a p q l T t.
    move=> Hp.
    rewrite (same_red_depth Hp).
    move:(unroll_preserves_type (lrec_depth L) Hp).

    move:(punroll _ _) (lunroll _ _)=> P' L'//=.

    case=>//.
    {
      move=>a0 p0 alts.
      case:ifP; last by case: (find_cont a0 l)=>[[t' Lp] | ].
      move=>_ {a p0} DOM OFT.
      case EQ: (find_cont a0 l)=>[[T' Lp]|];
        last by move: (dom_none' DOM EQ); rewrite/find_alt_ty; case: find_alt.
      move: (dom' DOM EQ); rewrite /find_alt_ty.
      case EQ': find_alt=>[[T'' rK]|]//= H.
      have Tt': T'' = T' by move: H=>[][][].
      move: Tt' rK EQ EQ' =>-> {T'' H}.
      case: eqP=>//; case: (boolP (T == T'))=>[/eqP<-|/eqP//] EQ {T'}.
      rewrite (eq_irrelevance EQ erefl)/= => rK EQ0 EQ1 [<-]{EQ Ps}.
      by apply/OFT; first by apply/EQ1.
    }

    {
      move=>p0 L0 a0 T0 l0 t0 K Hk Hfind.
      case:ifP ; last by case Hfind':(find_cont a0 l)=>[[T1 L1]|].

      move=>/andP[/andP[/eqP-> /eqP->] /eqP->].
      move:Hfind=>/eqP->.
      rewrite!eq_refl/=.
      case:ifP; last by case:eqP.
      move=>Heq; move:Heq t=>/eqP->{T} t.
      case:eqP=>p0'//.
      move:{p0'}(esym p0')=>Hesym.
      rewrite (eq_irrelevance Hesym erefl)=>//=.
      case:ifP=>//.
      move=>_ []<-//.
    }
  Qed.

End OperationalSemantics.

Section TraceEquivalence.

  (* single local type trace (MOVE TO Local.v) *)
  Definition rel_sl_trc := trace act -> l_ty -> Prop.
  Inductive sl_lts_ (r : rel_sl_trc) : rel_sl_trc :=
  | slt_end :
      @sl_lts_ r (tr_end _) l_end
  | slt_next a t L L' :
      do_act_l_ty L a == Some L' ->
      r t L' ->
      @sl_lts_ r (tr_next a t) L.

  Hint Constructors sl_lts_.
  Lemma sl_lts_monotone : monotone2 sl_lts_.
  Proof. pmonauto. Qed.
  Hint Resolve sl_lts_monotone : paco.

  Definition sl_lts t L := paco2 sl_lts_ bot2 t L.
  Definition sl_accepts TRACE L := sl_lts TRACE L.

  Definition rel_srl_trc := trace act -> rl_ty -> Prop.
  Inductive srl_lts_ (r : rel_srl_trc) : rel_srl_trc :=
  | srlt_end :
      @srl_lts_ r (tr_end _) rl_end
  | srlt_next a t L L' :
      do_act_lt L a = Some L' ->
      r t L' ->
      @srl_lts_ r (tr_next a t) L.

  Hint Constructors srl_lts_.
  Lemma srl_lts_monotone : monotone2 srl_lts_.
  Proof. pmonauto. Qed.
  Hint Resolve srl_lts_monotone : paco.

  Definition srl_lts t L := paco2 srl_lts_ bot2 t L.
  Definition srl_accepts TRACE L := srl_lts TRACE L.

  (* process local type trace *)
  Definition rel_proc_trc := trace rt_act -> Proc -> Prop.

  Inductive p_lts_ (r : rel_proc_trc) : rel_proc_trc :=
  | pt_end :
      p_lts_ r (tr_end _) Finish
  | pt_next A P P' TR :
      do_step_proc P A = Some P' ->
      r TR P' ->
      p_lts_ r (tr_next A TR) P
  .

  Lemma p_lts_monotone : monotone2 p_lts_.
  Proof. pmonauto.  Admitted.
  Hint Resolve p_lts_monotone : paco.

  Definition p_lts TR P := paco2 (p_lts_) bot2 TR P.

  Definition p_accepts PTRACE P := p_lts PTRACE P.

  Definition erase : trace rt_act -> trace act := trace_map erase_act.

  Lemma local_type_accepts_process_trace P L PTRACE:
    of_lt P L ->
    p_accepts PTRACE P ->
    sl_accepts (erase PTRACE) L.
  Proof.
  Admitted.

  Definition match_head F T TR :=
    match TR with
    | tr_next a _ =>
      if (F == subject a) && (T == object a) && (l_send == act_ty a)
         || (F == object a) && (T == subject a) && (l_recv == act_ty a)
      then Some a
      else None
    | _ => None
    end.

  Definition match_tail F T TR :=
    match TR with
    | tr_next a TR' =>
      if (F == subject a) && (T == object a) && (l_send == act_ty a)
         || (F == object a) && (T == subject a) && (l_recv == act_ty a)
      then TR'
      else TR
    | _ => TR
    end.

  Definition find_cont_dflt l Ty (Ks : seq (lbl * (mty * g_ty)))
    := match find_cont Ks l with
       | None => ohead Ks
       | Some (Ty', G) => if Ty == Ty' then Some (l, (Ty, G)) else ohead Ks
       end.

  Definition select_alt TRH (Ks : seq (lbl * (mty * g_ty)))
    := match TRH with
       | Some (mk_act _ _ _ l Ty) => find_cont_dflt l Ty Ks
       | None => ohead Ks
       end.

  CoFixpoint build_trace (TR : trace act) (g : g_ty) : trace act :=
    match n_unroll (rec_depth g) g with
    | g_msg F T Ks =>
      match select_alt (match_head F T TR) Ks with
      | Some K =>
        tr_next (mk_act l_send F T K.1 K.2.1)
                (tr_next (mk_act l_recv T F K.1 K.2.1)
                         (build_trace (match_tail F T TR) K.2.2))
      | None => tr_end _
      end
    | _ => tr_end _
    end.

  Definition build_trace' (TR : trace act) (g : g_ty) : trace act :=
    match g with
    | g_msg F T Ks =>
      match select_alt (match_head F T TR) Ks with
      | Some K =>
        tr_next (mk_act l_send F T K.1 K.2.1)
                (tr_next (mk_act l_recv T F K.1 K.2.1)
                         (build_trace (match_tail F T TR) K.2.2))
      | None => tr_end _
      end
    | _ => tr_end _
    end.

  Lemma trace_unr (T : trace act) : T = match T with
                                        | tr_next h t => tr_next h t
                                        | tr_end => tr_end _
                                        end.
  Proof. by case: T. Qed.

  Lemma build_trace_unr TR g : build_trace TR g = build_trace' TR (n_unroll (rec_depth g) g).
  Proof.
    rewrite (trace_unr (build_trace TR g)) /build_trace' /=.
    case: (n_unroll (rec_depth g) g) =>// F T C.
    by case: (select_alt (match_head F T TR) C).
  Qed.

  Definition env_unroll (iPe :  {fmap role -> l_ty})(Pe :  {fmap role -> rl_ty}) : Prop :=
    forall p, LUnroll (ilook iPe p) (look Pe p).

  (* this is a silly definition, but coercions drive me nuts *)
  Definition eproject_eq_some G iPe :
    eproject G == Some iPe -> eproject G.
      by move/eqP=>->.
  Defined.

  Lemma eproject_project_env G iPe (WF : well_formed G) (Hproj :eproject G == Some iPe):
        project_env WF = iPe.
  Proof.
  Admitted. (* this is a simple proof made annoying by depdent types *)

  Lemma build_accepts' C F T (r : trace act -> ig_ty -> Prop)
        (CIH : forall t g,
            non_empty_cont g -> r (build_trace t g) (ig_end (g_expand g)))
        (TR : trace act)
        (NE1 : ~~ nilp C)
        (NE2 : forall x, member x C -> non_empty_cont x.2.2)
    : paco2 g_lts_ r
            match ohead C with
            | Some K => tr_next (mk_act l_send F T K.1 K.2.1)
                                (tr_next (mk_act l_recv T F K.1 K.2.1)
                                         (build_trace TR K.2.2))
            | None => tr_end act
            end
            (ig_end (rg_msg F T
                            (fun l : lbl => match find_cont C l with
                                            | Some (Ty, G0) =>
                                              Some (Ty, g_expand G0)
                                            | None => None
                                            end))).
  Proof.
    move: NE1 NE2; case: C=>//=[[l [Ty G]]]/= C _ /(_ _ (or_introl erefl))-NE.
    apply/paco2_fold; apply: eg_trans;
      first by apply/st_unr/st_send=>/=; rewrite /extend eq_refl.
    left; apply/paco2_fold; apply: eg_trans;
      first by apply/st_recv; rewrite /extend eq_refl.
    by right; apply/CIH.
  Qed.

  Lemma build_accepts G TR :
    non_empty_cont G ->
    gty_accepts (build_trace TR G) G.
  Proof.
    rewrite /gty_accepts => EQ1.
    move EQ2: (build_trace TR G) => iG.
    move EQ3: (ig_end (g_expand G)) => cG.
    move: (conj EQ1 (conj EQ2 EQ3)) => {EQ1 EQ2 EQ3}.
    move=>/(ex_intro (fun=>_) TR)=> {TR}.
    move=>/(ex_intro (fun=>_) G)=> {G}.
    move: iG cG; apply/paco2_acc=>r _.
    move=>/(_ _ _ (ex_intro _ _ (ex_intro _ _ (conj _ (conj erefl erefl)))))-CIH.
    move=>TR' PG [iG][TR][H1][<-][<-] {TR' PG}.
    rewrite g_expand_once build_trace_unr.
    move: H1 =>/(ne_unr (rec_depth iG)); move: (n_unroll (rec_depth iG) iG)=>{iG}.
    case=>[|v|G|F T C] /=NE; try (by apply/paco2_fold; constructor).
    move: NE=>/andP-[NE1 /forallbP/forall_member/member_map-NE2].
    rewrite /select_alt/match_head/match_tail.
    case: TR=>[|[a p q l t] TR]/=; first by apply/build_accepts'.
    case: ifP=>[|_]; last by apply/build_accepts'.
    rewrite /find_cont_dflt => EQ.
    case EQ1: find_cont=>[[Ty G]|]; last by apply/build_accepts'.
    case: ifP=>[/eqP->{t}/=|_]; last by apply/build_accepts'.
    apply/paco2_fold; apply: eg_trans; first by apply/st_unr/st_send; rewrite EQ1.
    left; apply/paco2_fold; apply: eg_trans; first by apply/st_recv; rewrite EQ1.
    by right; apply/CIH/(NE2 (l, (Ty, G)))/find_member.
  Qed.

  Lemma build_subtrace p TR G L cL :
        (* we know things we could add as hyps here *)
    g_precond G ->
    project G p == Some L ->
    LUnroll L cL ->
    srl_accepts TR cL ->
    subtrace p TR (build_trace TR G).
    (* rewrite /sl_accepts. *)
    (* Print sl_lts_. *)
    (* Print do_act_l_ty. *)
    (* SearchAbout project. *)
    (* (* TODO: local types up to unrollings accept the same traces *)
    (*  *) *)
  Admitted.

  Definition of_lt_unr P cL :=
    exists L, of_lt P L /\ LUnroll L cL.

  (* TODO: Lorenzo *)
  Lemma sl_accepts_unr L cL TRACE :
    LUnroll L cL ->
    sl_accepts TRACE L ->
    srl_accepts TRACE cL.
  Admitted.

  Lemma not_srl_accepts_end h t :
    ~ srl_accepts (tr_next h t) rl_end.
  Admitted.

  Lemma proj_all_in G iPe p :
    project_all (participants G) G = Some iPe ->
    (p \in participants G) ->
    project G p = Some (ilook iPe p).
  Admitted.

  Lemma proj_all_notin G iPe p :
    project_all (participants G) G = Some iPe ->
    (p \notin participants G) ->
    ilook iPe p = l_end.
  Admitted.

  (* TODO: Francisco *)
  Lemma subtrace_end p G :
    p \notin participants G ->
    subtrace p (tr_end act) (build_trace (tr_end act) G).
  Admitted.

  Theorem process_traces_are_global_types G p iPe P PTRACE:
    eproject G == Some iPe ->
    of_lt_unr P (l_expand (ilook iPe p)) ->
    p_accepts PTRACE P ->
    exists TRACE, (* constructed with the build function *)
      gty_accepts TRACE G /\ subtrace p (erase PTRACE) TRACE.
  Proof.
    move=>/eqP-Hproj [L][Hoft] Hunr Hpacc.
    move: Hproj; rewrite /eproject; case: ifP=>//Hpre Hproj.
    have NE: non_empty_cont G by move: Hpre=>/andP-[].
    exists (build_trace (erase PTRACE) G); split; first by apply: build_accepts.
    case: (boolP (p \in participants G)).
    - move=>/(proj_all_in Hproj); move: (ilook iPe p) Hunr=>iL Hunr /eqP-{}Hproj.
      move: Hpacc=>/(local_type_accepts_process_trace Hoft)/(sl_accepts_unr Hunr).
      apply: (build_subtrace Hpre Hproj).
      move: Hpre=>/andP-[/andP-[CG GG] _].
      move: (proj_lclosed CG Hproj) (project_guarded Hproj) (proj_lne NE Hproj) => CL GL LNE.
      by apply: l_expand_unr.
    - move=>p_notin_G; move: (proj_all_notin Hproj p_notin_G)=>EQ; move: EQ Hunr=>->.
      rewrite l_expand_once/==>Hunr.
      move: Hpacc=>/(local_type_accepts_process_trace Hoft)/(sl_accepts_unr Hunr).
      rewrite (trace_unr (erase PTRACE))/=.
      case: PTRACE=>[|h t]; last by move=>/not_srl_accepts_end.
      by move=>_; apply/subtrace_end.
  Qed.

End TraceEquivalence.
