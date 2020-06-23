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

(*
l_rec l_msg a p [(0, (t1, l_msg a r end)), (1, (t2, l_msg a q 0))]

l_msg a p [(0, t1, l_msg a r end),
(1, (t2, l_rec l_msg a q l_msg a p [(0, t1, l_msg a r end), (1, t2, 0)]0))]
*)

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

Notation finish := wt_end.
Notation jump := wt_jump.
Notation loop := wt_loop.

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

Declare Scope proc_scope.
Notation " \lbl l1 , x ':' T1 ; p1"
  := (l1,
      existT (fun T => {L & coq_ty T -> wt_proc L}) T1
             (existT (fun L => coq_ty T1 -> wt_proc L)
                     _ (fun x => p1)))
       (at level 0, x ident, p1 constr at level 200) : proc_scope.

Notation "[ 'alts' | a1 | .. | a2 | an ]"
  := (cons_alt a1 .. (cons_alt a2 (sing_alt an)) .. )
       (at level 0,
        a1 constr at level 200,
        a2 constr at level 200,
        an constr at level 200) : proc_scope.

Notation "\branch" := (wt_recv) (at level 0) : proc_scope.
Notation "\recv" := (fun p a => wt_recv p (sing_alt a))
                      (at level 0) : proc_scope.

Lemma if_proc_wt {L} (b : bool) (p1 p2 : wt_proc L) :
  of_lt (if b then proj1_sig p1 else proj1_sig p2) L.
Proof. by case: b; [case: p1|case:p2]. Qed.

Definition if_proc {L} (b : bool) (p1 p2 : wt_proc L) : wt_proc L
  := exist _ _ (if_proc_wt b p1 p2).

Notation "'if' c 'then' vT 'else' vF" := (if_proc c vT vF) : proc_scope.

Definition typed_proc := {L : l_ty & wt_proc L}.
Notation "[ 'proc' p ]" := (existT (fun L => wt_proc L) _ p) (at level 200) : proc_scope.

(* Smart constructor and helpers for send *)
Lemma find_cont_sing l T (L : l_ty)
  : find_cont [:: (l, (T, L))] l == Some (T, L).
Proof. by rewrite /find_cont/extend eq_refl. Qed.

Definition wt_send p l T (pl : coq_ty T) L (P : wt_proc L)
  : wt_proc (l_msg l_send p [::(l, (T, L))])
  := exist _ _ (t_Send p pl (of_wt_proc P) (find_cont_sing l T L)).

Fixpoint unique_labels (l : seq (lbl * (mty * l_ty)))
  := match l with
     | [::] => true
     | h :: l => all (fun x => h.1 != x.1) l && (unique_labels l)
     end.

Lemma fnd_app l (a1 a2 : seq (lbl * (mty * l_ty))) :
  find_cont (a1 ++ a2) l =
  if find_cont a1 l is Some (Ty, L) then Some (Ty, L)
  else find_cont a2 l.
Proof.
  by elim: a1=>//= [][l'][Ty'] L' a1 Ih; rewrite /extend; case: ifP.
Qed.
Lemma unique_cons a1 h2 a2 :
  unique_labels (a1 ++ (h2 :: a2)) ->
  all (fun x => h2.1 != x.1) (a1 ++ a2) /\ unique_labels (a1 ++ a2).
Proof.
  elim: a1=>[/andP//|h1 a1 Ih]/=; rewrite !all_cat/==>/andP[/andP[->/andP[]]].
  by rewrite eq_sym=>->->/Ih; rewrite all_cat.
Qed.

Lemma unique_app_sym a1 a2
  : unique_labels (a1 ++ a2) -> unique_labels (a2 ++ a1).
Proof.
  elim: a2 a1 =>[|h2 a2 Ih]//= a1; first by rewrite cats0.
  by move=>/unique_cons; rewrite !all_cat=>[][/andP-[->->]/Ih].
Qed.

Lemma unique_app_find l Ty (L : l_ty) a1 a2 :
  unique_labels (a1 ++ a2) ->
  find_cont a2 l == Some (Ty, L) ->
  find_cont a1 l = None.
Proof.
  move=>/unique_app_sym; elim: a2=>//= [][l2][Ty2]L2 a2 Ih/=.
  rewrite /extend; case: ifP=>[/eqP->|].
  - rewrite all_cat=>/andP-[/andP-[_ ALL] _ _] {Ih a2 l2 Ty2 L2 Ty L}; move: ALL.
    by elim: a1=>//= [][l1 v1]/= a1 Ih; rewrite /extend eq_sym=>/andP-[/negPf->].
  - by move=> _ /andP-[_].
Qed.

Lemma fnd_app_r l Ty (L : l_ty) a1 a2 :
  unique_labels (a1 ++ a2) ->
  find_cont a2 l == Some (Ty, L) ->
  find_cont (a1 ++ a2) l = Some (Ty, L).
Proof.
    by rewrite fnd_app=>DISJ FND; rewrite (unique_app_find DISJ FND); apply/eqP.
Qed.

Lemma skipL_wt p a1 a2 (P2 : wt_proc (l_msg l_send p a2))
      (H : unique_labels (a1 ++ a2))
  : of_lt (proj1_sig P2) (l_msg l_send p (a1 ++ a2)).
Proof.
  case: P2=>//= x; case EQ: _ / => [||||q L a Ty l pl P o fnd] //.
  move: EQ fnd=>[<-<-] /eqP-FND {q a}; apply/(t_Send p pl o)/eqP.
  by move: FND=>/eqP; apply/fnd_app_r.
Qed.

Lemma skipR_wt p a1 a2 (P1 : wt_proc (l_msg l_send p a1))
      (H : unique_labels (a1 ++ a2))
  : of_lt (proj1_sig P1) (l_msg l_send p (a1 ++ a2)).
Proof.
  case: P1=>//= x; case EQ: _ / => [||||q L a Ty l pl P o fnd] //.
  move: EQ fnd=>[<-<-] /eqP-FND {q a}; apply (t_Send p pl o).
  by rewrite fnd_app FND.
Qed.

Lemma sel_wt b p a1 a2
      (P1 : wt_proc (l_msg l_send p a1)) (P2 : wt_proc (l_msg l_send p a2))
      (H : unique_labels (a1 ++ a2))
  : of_lt (if b then proj1_sig P1 else proj1_sig P2) (l_msg l_send p (a1 ++ a2)).
Proof. by case: b; [apply/skipR_wt | apply/skipL_wt]. Qed.

Definition sel_skipL p a1 a2 (P2 : wt_proc (l_msg l_send p a2))
           (H : unique_labels (a1 ++ a2))
  : wt_proc (l_msg l_send p (a1 ++ a2))
  := exist _ _ (skipL_wt P2 H).
Arguments sel_skipL p a1 [a2] _ _.

Definition sel_skipR p a1 a2 (P1 : wt_proc (l_msg l_send p a1))
           (H : unique_labels (a1 ++ a2))
  : wt_proc (l_msg l_send p (a1 ++ a2)) := exist _ _ (skipR_wt P1 H).
Arguments sel_skipR p [a1] a2 _ _.

Definition wt_sel b p a1 a2
           (P1 : wt_proc (l_msg l_send p a1))
           (P2 : wt_proc (l_msg l_send p a2))
           (H : unique_labels (a1 ++ a2))
  : wt_proc (l_msg l_send p (a1 ++ a2))
  := exist _ _ (sel_wt b P1 P2 H).

Inductive sel_alt : Type :=
| if_alt (b : bool) (l : lbl)  T (pl : coq_ty T) L (P : wt_proc L)
| df_alt (l : lbl) T (pl : coq_ty T) L (P : wt_proc L)
| sk_alt (l : lbl) (T : mty) (L : l_ty)
.

Notation "'\case' b '=>' l ',' pl '\as' T '!' P"
  := (if_alt b l (T:=T) pl P)
       (at level 0, P constr at level 200) : proc_scope.
Notation " '\otherwise' '=>' l , pl '\as' T '!' P"
  := (df_alt l (T:=T) pl P) (at level 0, P constr at level 200)
     : proc_scope.
Notation "'\skip' '=>' l , pl '!' P"
  := (sk_alt l pl P) (at level 0, P constr at level 200)
     : proc_scope.
Notation "[ 'sel' '|' a1 '|' .. '|' an ]"
  := (cons a1 .. (cons an (@nil sel_alt)) .. )
       (at level 0,
        a1 constr at level 200,
        an constr at level 200) : proc_scope.

Definition get_alt_lt (s : sel_alt) :=
  match s with
  | if_alt b l T _ L _ => (l, (T, L))
  | df_alt l T _ L _ => (l, (T, L))
  | sk_alt l T L  => (l, (T, L))
  end.

Definition to_lt_sel_alts (s : seq sel_alt) : seq (lbl * (mty * l_ty))
  := [seq get_alt_lt x | x <- s].

Definition is_dflt (s : sel_alt) :=
  match s with
  | df_alt _ _ _ _ _ => true
  | _ => false
  end.

Definition is_skip (s : sel_alt) :=
  match s with
  | sk_alt _ _ _ => true
  | _ => false
  end.

Fixpoint has_single_default (s : seq sel_alt) :=
  match s with
  | [::] => false
  | h :: t => if is_dflt h then all (fun x => is_skip x) t
              else has_single_default t
  end.

Lemma has_single_default_nil : has_single_default [::] -> False.
Proof. by []. Qed.

Lemma unique_labels_tail h t :
  unique_labels (h :: t) -> unique_labels t.
Proof. by rewrite /==>/andP-[]. Qed.

Fixpoint wt_select p (s : seq sel_alt)
  : has_single_default s ->
    unique_labels (to_lt_sel_alts s) ->
    wt_proc (l_msg l_send p (to_lt_sel_alts s))
  := match s with
     | [::] =>
       fun H _ =>
         match has_single_default_nil H with end
     | h :: t =>
       match h
             return
             has_single_default (h::t) ->
             unique_labels (to_lt_sel_alts (h::t)) ->
             wt_proc (l_msg l_send p (to_lt_sel_alts (h::t)))
       with
       | if_alt b l _ pl _ k =>
         fun H1 H2 =>
           wt_sel b (wt_send p l pl k)
                  (@wt_select p t H1 (unique_labels_tail H2))
                  H2

       | sk_alt l pl k =>
         fun H1 H2 =>
           sel_skipL p [:: (l, (pl, k))]
                     (@wt_select p t H1 (unique_labels_tail H2))
                     H2
       | df_alt l _ pl _ k =>
         fun H1 H2 =>
           sel_skipR
             p (to_lt_sel_alts t)
             (wt_send p l pl k)
             H2
       end
     end.

Notation "'\select' p a" := (@wt_select p a is_true_true is_true_true)
                            (at level 0, p at level 0, a constr at level 99).
Notation "\send" := wt_send.

(* Notation " [ 'out' p ',' l ',' e '\as' T ]; p1 " *)
(*   := (wt_send p l (T:=T) e p1) (at level 0, right associativity) : proc_scope. *)

Notation "a '\skipL' pr"
  := (sel_skipL _ a pr is_true_true)
       (at level 0, right associativity) : proc_scope.

Notation "pr '\skipR' a"
  := (sel_skipR _ a pr is_true_true)
       (at level 1, left associativity) : proc_scope.

(* Notation " 'select' b 'then' pT 'else' pF " := (wt_sel b pT pF is_true_true) (at level 200). *)

Section Examples.
Open Scope proc_scope.
Let p := roleid.mk_atom 0.
Definition test1 b1 b2 :=
  [proc
     \select p
     [sel
     | \case b1   => 0 , 100 \as T_nat ! wt_end
     | \skip      => 4 , T_nat         ! l_end
     | \case b2   => 3 , 10 \as T_nat  ! wt_end
     | \otherwise => 1 , b1 \as T_bool ! wt_end
     | \skip      => 2 , T_nat         ! l_end
     ]
  ].

Eval compute in fun b1 b2 => projT1 (test1 b1 b2).
Eval compute in fun b1 b2 => get_proc (projT2 (test1 b1 b2)).

Definition test : typed_proc
  := [proc
        \branch (roleid.mk_atom 0)
        [alts
        | \lbl 0, x : T_bool; if x then wt_end else wt_end
        | \lbl 1, x : T_nat ; wt_end
        ]
     ].
Eval compute in projT1 test.
Eval compute in get_proc (projT2 test).

Definition Bye := 0.
Definition Ping := 1.
Definition Pong := 1.

Definition ping_pong_server p :=
  [proc
     loop (
       \branch p
        [alts
        | \lbl Bye, _ : T_unit;
            finish
        | \lbl Ping, x : T_nat;
            (\send p Pong x (jump 0))
        ]
     )
  ].


Definition ping_pong_client0 p :=
  [proc
     loop (
       \select p
        [sel
        | \otherwise => Bye, tt \as T_unit ! finish
        | \skip => Ping, T_nat ! l_msg l_recv p [:: (Pong, (T_nat, l_var 0))]

        ]
     )
  ].

Definition ping_pong_client1 p :=
  [proc
     loop (
       \select p
        [sel
        | \skip      => Bye , T_unit ! l_end
        | \otherwise => Ping, 1 \as T_nat !
              (\recv p \lbl Pong, x : T_nat; (jump 0))
        ]
     )
  ].

Definition ping_pong_client2 p :=
  [proc
     \select p
     [sel
     | \otherwise => Bye, tt \as T_unit ! finish
     | \skip => Ping, T_nat !
             l_msg l_recv p
             [:: (Pong, (T_nat, projT1 (ping_pong_client1 p)))]
     ]
  ].

Goal projT1 (ping_pong_client2 p) = lunroll 1 (projT1 (ping_pong_client1 p)).
  by [].
Qed.


Close Scope proc_scope.
End Examples.

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
