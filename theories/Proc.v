From mathcomp Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco2.

Require Import MPST.Actions.
Require Import MPST.AtomSets.
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

(* open variable d, with process P2 in process P1 *)
Fixpoint p_open (d : nat) (P2 P1 : Proc) : Proc :=
  match P1 with
  | Finish => Finish
  | Jump v => if v == d then P2 else P1
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

(* (* alternative definition with the order swapped *) *)
(* Fixpoint punroll' d P := *)
(*     match P with *)
(*     | Loop P' => *)
(*       match d with *)
(*       | 0 => P *)
(*       | d.+1 => punroll' d (p_open 0 P P') *)
(*       end *)
(*     | _ => P *)
(*     end. *)

(*   Fixpoint lunroll' d G := *)
(*       match G with *)
(*       | l_rec G' => *)
(*         match d with *)
(*         | 0 => G *)
(*         | d.+1 => lunroll d (l_open 0 G G') *)
(*         end *)
(*       | _ => G *)
(*     end. *)

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

Definition wt_proc L
  := { P : Proc  | of_lt P L }.


(* Destructors *)
Definition get_proc L (P : wt_proc L) : Proc := (proj1_sig P).
Definition of_wt_proc L (P : wt_proc L) : of_lt (get_proc P) L := proj2_sig P.

(* Constructors *)
Definition wt_end : wt_proc l_end :=  exist _ _ t_Finish.
Definition wt_jump v : wt_proc (l_var v) :=  exist _ _ (t_Jump v).
Definition wt_loop L (P : wt_proc L) : wt_proc (l_rec L)
  := exist _ _ (t_Loop (of_wt_proc P)).

(* Smart constructor and helpers for recv *)
Definition wt_alt : Type := lbl * {T & {L & coq_ty T -> wt_proc L}}.

Fixpoint to_proc_alts (alts : seq wt_alt) (a0 : wt_alt) : Alts
  := match alts with
     | [::] =>
       A_sing a0.1
              (fun x => get_proc (projT2 (projT2 a0.2) x))
     | a1 :: alts =>
       A_cons a1.1
              (fun x => get_proc (projT2 (projT2 a1.2) x))
              (to_proc_alts alts a0)
     end.

Fixpoint to_lt_alts (alts : seq wt_alt) (a0 : wt_alt) : seq (lbl * (mty * l_ty))
  := match alts with
     | [::] => [:: (a0.1, (projT1 a0.2, projT1 (projT2 a0.2)))]
     | a1 :: alts =>
       (a1.1, (projT1 a1.2, projT1 (projT2 a1.2))) :: to_lt_alts alts a0
     end.

Lemma same_dom_alts (a : seq wt_alt) (a0 : wt_alt)
  : same_dom (find_alt_ty (to_proc_alts a a0)) (find_cont (to_lt_alts a a0)).
Proof.
  elim: a=>[|a1 alts Ih]/=; [case: a0| case: a1]; move=>l [Ty [L P]] l' Ty'/=;
    split=>[][x]/=; rewrite /extend/find_alt_ty/=; case: ifP=>[/eqP->|]//=;
    rewrite ?eq_refl/=; try rewrite eq_sym=>->; try move=>[-> _];
    try (by exists L); try (by exists tt).
  - case EQ: find_alt=>[[Ty0 x0]|]//= [<- _].
    have: find_alt_ty (to_proc_alts alts a0) l' = Some (Ty0, tt)
      by rewrite /find_alt_ty EQ/=.
    by move=>/(dom Ih).
  - move=>/(dom' Ih)-[][]; rewrite /find_alt_ty; case: find_alt=>//[][Ty0]/=_[<-].
    by exists tt.
Qed.

Lemma to_alts_wt (a : seq wt_alt) (a0 : wt_alt)
  : forall l Ty rK L,
    find_alt (to_proc_alts a a0) l = Some (existT _ Ty rK) ->
    find_cont (to_lt_alts a a0) l = Some (Ty, L) ->
    forall pl, of_lt (rK pl) L.
Proof.
  elim: a=>[|a1 alts Ih]; [case: a0|case: a1];
    move=>l0 [Ty0] [L0] P0 l Ty rK L/=; rewrite /extend eq_sym;
    case: ifP=>[_ {l0 l}|NE]//.
  - move=>[EQ]; move: EQ P0=>-> P0 H {Ty0}.
    rewrite -(Eqdep_dec.inj_pair2_eq_dec _ _ _ _ _ _ H) => {H};
      last by move=>x y; apply/(decP eqP).
    by move=>[<-] pl; apply: (of_wt_proc (P0 pl)).
  - move=>[EQ]; move: EQ P0=>-> P0 H {Ty0}.
    rewrite -(Eqdep_dec.inj_pair2_eq_dec _ _ _ _ _ _ H) => {H};
      last by move=>x y; apply/(decP eqP).
    by move=>[<-] pl; apply: (of_wt_proc (P0 pl)).
  - by move=> H1 H2; apply: Ih; [apply: H1 | apply: H2].
Qed.
Arguments to_alts_wt : clear implicits.

Definition wt_alts := (seq wt_alt * wt_alt)%type.

(* Well-typed recv *)
Definition wt_recv (p : role) (a : wt_alts)
  : wt_proc (l_msg l_recv p (to_lt_alts a.1 a.2))
  := exist _ _ (t_Recv p (same_dom_alts a.1 a.2) (to_alts_wt a.1 a.2)).

Definition sing_alt a : wt_alts := ([::], a).
Definition cons_alt a alts : wt_alts := (a :: alts.1, alts.2).

Definition P_alt_lty T := fun L => coq_ty T -> wt_proc L.
Definition P_alt_pl_ty := fun T => {L & P_alt_lty T L}.

Declare Scope proc_scope.
Notation " l1 [ x ':' T1 '];' p1"
  := (l1,
      existT (fun T => {L & coq_ty T -> wt_proc L}) T1
             (existT (fun L => coq_ty T1 -> wt_proc L)
                     _ (fun x => p1)))
       (at level 0, x ident) : proc_scope.

Notation "'branch' p { a1 | .. | a2 | an }"
  := (wt_recv p (cons_alt a1 .. (cons_alt a2 (sing_alt an)) .. ))
       (at level 0, a1 at level 99, a2 at level 99, an at level 99) : proc_scope.

Notation recv p a := (wt_recv p (sing_alt a)).

Lemma if_proc_wt {L} (b : bool) (p1 p2 : wt_proc L) :
  of_lt (if b then proj1_sig p1 else proj1_sig p2) L.
Proof. by case: b; [case: p1|case:p2]. Qed.

Definition if_proc {L} (b : bool) (p1 p2 : wt_proc L) : wt_proc L
  := exist _ _ (if_proc_wt b p1 p2).

Notation "'if' c 'then' vT 'else' vF" := (if_proc c vT vF) : proc_scope.

Definition typed_proc := {L : l_ty & wt_proc L}.
Notation "'[proc' p ']'" := (existT (fun L => wt_proc L) _ p) (at level 200) : proc_scope.

Open Scope proc_scope.
Definition test : typed_proc
  := [proc
        recv (roleid.mk_atom 0) 0 [ x : T_bool ]; if x then wt_end else wt_end
     ].
Eval compute in projT1 test.
Eval compute in get_proc (projT2 test).
(* TODO: 'if' is a problem, and does not reduce, maybe a 'proc_if' *)

Lemma find_cont_sing l T (L : l_ty)
  : find_cont [:: (l, (T, L))] l == Some (T, L).
Proof. by rewrite /find_cont/extend eq_refl. Qed.

Definition wt_send p l T (pl : coq_ty T) P : wt_proc :=
  exist _ (_, _) (t_Send p pl (of_wt_proc P) (find_cont_sing l T (get_ty P))).

Definition wt_alt : Type
  := lbl * {T & {L & { f : coq_ty T -> Proc | forall pl, of_lt (f pl) L}}}.
Definition to_proc_alt a :=
  (a.1, )
Definition wt_cont :=
  seq .
Fixpoint get_proc_alts (t : wt_cont) :=
  match t with
  | [::] => [::]
  | h :: t =>
Definition wt_recv p (alts : )

Fixpoint wt_select T (f : coq_ty T -> lbl) (alts : seq wt_proc) : coq_ty T -> wt_proc.

Notation "'SELECT' e 'WITH' p1 '=>' c1 '|' .. '|' pn '=>' cn 'END'"
  := (if e is p1 then c1 else (.. (if e is pn then cn else any _) ..)) (at level 0, p1 pattern, pn pattern).

Require Extraction.
Inductive test := C1 of nat | C2 of bool | C3.
Definition is_one :=
  (fun n =>
    match n with
    | C1 _ => true
    | _ => match n with
           | C2 b => b
           | _ => true
           end
    end).
Set Extraction Flag 2047.
Extraction is_one.
.


Check (select true with true => false | false => true | _ => false end).

(* Unset Printing Notations. *)

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

  Lemma find_cont_open n L L' Ks Ty l :
    find_cont [seq (K.1, (K.2.1, l_open n L' K.2.2)) | K <- Ks] l = Some (Ty, L) ->
    exists L0,
      find_cont Ks l = Some (Ty, L0) /\ L = l_open n L' L0.
  Proof.
    elim: Ks=>//= [][l'][Ty'] L0 Ks Ih.
    by rewrite /extend/=; case:ifP=>// _ [-><-]; exists L0.
  Qed.

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
    - by case: ifP=>//; constructor.
    - apply/t_Recv;
        first by apply/(same_dom_trans _ (same_dom_map _ _))/(same_dom_trans _ DOM)/find_alt_ty_open.
      move=> l Ty rK L0 /find_alt_open-[rK'] [EQ0->] /find_cont_open-[L1][EQ1->] .
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

  Definition rel_proc_trc := trace rt_act -> Proc -> Prop.

  Inductive p_lts_ (r : rel_proc_trc) : rel_proc_trc :=
  | pt_end :
      p_lts_ r (tr_end _) Finish
  | pt_next A P P' TR :
      do_step_proc P A = Some P' ->
      r TR P' ->
      p_lts_ r (tr_next A TR) P
  .

  Lemma p_lts_monotone P : monotone2 (l_trc_ P).
  Proof. pmonauto. Admitted.

  Definition p_lts TR P := paco2 (p_lts_) bot2 TR P.


  Definition p_accepts PTRACE P := p_lts PTRACE P.

  Definition erase : trace rt_act -> trace act := trace_map erase_act.

  Theorem process_traces_are_global_types G p L P PTRACE TRACE:
    project G p == Some L ->
    of_lt P L ->
    p_accepts PTRACE P ->
    gty_accepts TRACE G ->
    subtrace p (erase PTRACE) TRACE.
  Proof.

  Abort.

End TraceEquivalence.


(* Code Extraction *)

From Coq Require Extraction.
Module MP.
  Parameter t : Type -> Type.

  Parameter send : forall T, role -> lbl -> T -> t unit.
  (* Extract Constant send => "ocaml_send". *)

  Parameter recv : (lbl -> t unit) -> t unit.
  Parameter recv_one : forall T, role -> t T.

  Parameter bind : forall T1 T2, t T1 -> (T1 -> t T2) -> t T2.

  Parameter pure : forall T1, T1 -> t T1.

  Parameter loop : forall T1, nat -> t T1 -> t T1.
  Parameter set_current: nat -> t unit.
End MP.


(*

Fixpoint gen_proc T (n:nat) (p : Proc T): MP.t unit
  := match p with
    | Finish => MP.pure tt
    | Send r _ _ _ l x p2 _ =>
      MP.bind (MP.send r l x) (fun _=> gen_proc n p2)
    | Recv a r alts =>
      let base_case := fun=> MP.pure tt in
      MP.recv (@gen_alts a n r alts base_case)

    | Loop _ p =>
      MP.loop n (gen_proc (n+1) p)

    | Jump x => MP.set_current (n - x - 1)
     end
with gen_alts (a :seq (lbl * (mty * l_ty)))
              (n:nat) (r : role) (alts : Alts a)
              (f : (lbl -> MP.t unit))
     : (lbl -> MP.t unit) :=
       let new_f L T (dproc : coq_ty T -> Proc L) l (label : lbl) : MP.t unit :=
           if label == l then
             MP.bind
               (MP.recv_one (coq_ty T) r)
               (fun d=> gen_proc n (dproc d))
           else
             f label
       in
       match alts with
       | A_sing T _ l dproc =>
         new_f _ T dproc l
       | A_cons T _ a l dproc alts =>
         gen_alts n r alts (new_f _ T dproc l)
       end.

End CodeExtraction.

Section CaseStudies.
(* replace by lunroll *)
Fixpoint unfold l :=
  match l with
    | l_end => l_end
    | l_var v => l_var v
    | l_msg a r Ks =>
      l_msg a r
            (map
               (fun en =>
                  let:
                       (lbl, (pl, l)) := en
                  in
                  (lbl, (pl,  unfold l)))
               Ks)
    | l_rec l => l_open 0 (l_rec l) (unfold l)
  end.

(* convenience definition for conditional processes *)
Definition IFP L (n : bool) (p : Proc L) (p' : Proc L) :=
  if n then p else p'.

(* Fixpoint proc_lty :
 *)

(* Some examples *)

(* the finished process *)
Definition p11 := Finish.
Definition ep11 := Eval compute in gen_proc 0 p11.
(* Extraction ep11. *)

Axiom C S : role. (* two roles *)

(* From mathcomp Require Import finmap. *)
(* Definition lbl_one : lbl := Lbl.fresh fset0. *)
(* we may want more "computable" labels *)

Parameter lbl_A lbl_B lbl_C : lbl.

(* receive a natural and end *)
Definition p1 := Recv C (@A_sing T_nat  _ lbl_A (fun=> Finish)).
Definition ep1 := Eval compute in gen_proc 0 p1.
(* Extraction ep1. *)

(* receive one of two labels and end *)
Definition p2 := Recv C (@A_cons T_nat _ _ lbl_A (fun=> Finish)
                                 (@A_sing T_nat _ lbl_B (fun=> Finish))).
Definition ep2 := Eval compute in gen_proc 0 p2.
(* Extraction ep2. *)

(* recursive process that receives or stops *)
Definition p3 :=
  Loop(Recv C (@A_cons T_nat _ _ lbl_A (fun=> Finish) (@A_sing T_nat  _ lbl_B (fun=> Jump 0)))).
Definition ep3 := Eval compute in gen_proc 0 p3.
(* Extraction ep3. *)

(* nested recursion *)
Definition p4 :=
  Loop(Loop(Recv C (@A_cons T_nat _ _ lbl_A (fun=> Finish) (@A_cons T_nat _ _ lbl_B (fun=> Jump 0) (@A_sing T_nat _ lbl_C (fun=> Jump 1)))))).
Definition ep4 := Eval compute in gen_proc 0 p4.
(* Extraction ep4. *)

(* Ping pong example *)

Parameter Ping Pong Bye : lbl.  (* the needed labels *)

Definition PP_C : l_ty :=
  l_rec
    (l_msg l_send S
           [:: (Bye, (T_unit, l_end))
            ; (Ping, (T_nat, l_msg l_recv S
                                   [:: (Pong, (T_nat, l_var 0))]))]).

Definition PP_S : l_ty :=
  l_rec
    (l_msg l_recv C
           [:: (Bye, (T_unit, l_end))
            ; (Ping, (T_nat, l_msg l_send C
                                   [:: (Pong, (T_nat, l_var 0))]))]).

(* server: answers the pings with the same data *)
Definition PingPongServer : Proc PP_S.
  refine (Loop (@Recv _ C _)).
  (*alts*)
  refine (@A_cons T_unit _ _ Bye (fun=> Finish)
                  (@A_sing T_nat  _ Ping (fun d=> _))).
  refine (@Send C _ _ T_nat Pong d (Jump 0) _).
  apply mem_head.
Defined.

(* the client that always says bye *)
Definition PingPongClientBye : Proc PP_C.
  refine (Loop (@Send S _ _ T_unit Bye tt Finish _)).
  apply mem_head.
Qed.

(* sends ping, waits for pong, repeat for ever *)
Definition PingPongClient1 : Proc PP_C.
  refine (Loop (@Send S _ _ T_nat Ping 7 (@Recv _ S _) _)).
  (* alts *)
  refine (@A_sing T_nat  _ Pong (fun=> Jump 0)).
  (* proof that we used the labels under the right type *)
  apply (@mem_drop 1)=>//=.
  apply mem_head.
Defined.

(* sends ping, waits for pong, sends bye *)
Definition PingPongClient2 : Proc PP_C.
  refine (Loop (@Send S _ _ T_nat Ping 7 (@Recv _ S _) _)).
  (* alts *)
  refine (@A_sing T_nat _ Pong (fun=> _)).

  refine (@Send S _ _ T_unit Bye tt Finish _).
  apply mem_head.

  apply (@mem_drop 1)=>//=.
  (* ?? <- fails because it should have unrolled the protocol *)
Abort.

Definition PP_C_unrolled := Eval compute in unfold PP_C.
(* Print PP_C_unrolled. *)

Definition PingPongClient2 : Proc PP_C_unrolled.
  rewrite/PP_C_unrolled. (* not necessary, just for convenience *)
  refine (@Send S _ _ T_nat Ping 3 (@Recv _ S _) _).
  (* alts *)
  refine (@A_sing T_nat _ Pong (fun=> _))=>//=.
  refine PingPongClientBye.

  apply (@mem_drop 1)=>//=.
  apply mem_head.
Defined.

Definition ppc2 := Eval compute in gen_proc 0 PingPongClient2.
(* Extraction ppc2. *)

(* sends ping, waits for pong, repeats while payload is not 3 *)
Definition PingPongClient3 : Proc PP_C_unrolled.
  refine (@Send S _ _ T_nat Ping 3 (@Recv _ S _) _).
  (* alts *)
  refine (@A_sing T_nat _ Pong (fun n=> _))=>//=.
  refine (Loop _).
  (* finish if you got 3 *)
  refine (IFP (n == 3) (@Send S _ _ T_unit Bye tt Finish _) _).

  apply mem_head.

  refine (@Send S _ _ T_nat Ping 7 (@Recv _ S _) _).
  refine (@A_sing T_nat _ Pong (fun=> _)).
  refine (Jump 0).

  apply (@mem_drop 1)=>/=.
  rewrite drop0.
  apply mem_head.

  apply (@mem_drop 1)=>//=.
  apply mem_head.
Defined.

Definition ppc3 := Eval compute in gen_proc 0 PingPongClient3.
(* Extraction ppc3. *)
*)
