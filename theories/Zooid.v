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
Require Import MPST.Proc.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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
Inductive wt_alt : lbl * (mty * l_ty) -> Type
  := | wt_cont l T L : (coq_ty T -> wt_proc L) -> wt_alt (l, (T, L)).

Definition app L (a : wt_alt L) : coq_ty L.2.1 -> wt_proc L.2.2 :=
  match a with
  | wt_cont _ _ _ f => f
  end.

Inductive wt_alts : seq (lbl * (mty * l_ty)) -> Type :=
| wta_sing L : wt_alt L -> wt_alts [:: L]
| wta_cons L Ls : wt_alt L -> wt_alts Ls -> wt_alts (L :: Ls).

Fixpoint mk_proc_alts L (alts : wt_alts L) : Alts
  := match alts with
     | wta_sing L f => A_sing L.1 (fun x => get_proc (app f x))
     | wta_cons L Ls f fs
       => A_cons L.1 (fun x => get_proc (app f x)) (mk_proc_alts fs)
     end.

Lemma same_dom_alts L (a : wt_alts L)
  : same_dom (find_alt_ty (mk_proc_alts a)) (find_cont L).
Proof.
  elim: a=>[{}L f|{}L Ls f a Ih]/=; case: L f=>[l[T L]] f l' T';
    rewrite /extend/empty/find_alt_ty/=; case: ifP=>[/eqP->|]//=;
    rewrite ?eq_refl; try rewrite eq_sym=>->; split=>[][x]//=[];
    try move=>[-> _]; try (by exists L); try (by exists tt).
  - case EQ: find_alt=>[[Ty0 x0]|]//= [<- _].
    have: find_alt_ty (mk_proc_alts a) l' = Some (Ty0, tt)
      by rewrite /find_alt_ty EQ/=.
    by move=>/(dom Ih).
  - move=>/(dom' Ih)-[][]; rewrite /find_alt_ty; case: find_alt=>//[][Ty0]/=_[<-].
    by exists tt.
Qed.

Lemma to_alts_wt Ls (a : wt_alts Ls)
  : forall l Ty rK L,
    find_alt (mk_proc_alts a) l = Some (existT _ Ty rK) ->
    find_cont Ls l = Some (Ty, L) ->
    forall pl, of_lt (rK pl) L.
Proof.
  elim: a=>[L f|L {}Ls f a Ih]; case: L f=>[l[T L]] f/= l' T' rK L'/=;
    rewrite /extend eq_sym; case: ifP=>[_ {l'}|NE]//.
  - move=>[EQ]; move: EQ f=>-> f H {T}.
    rewrite -(Eqdep_dec.inj_pair2_eq_dec _ _ _ _ _ _ H) => {H};
      last by move=>x y; apply/(decP eqP).
    by move=>[<-] pl; apply: (of_wt_proc (app f pl)).
  - move=>[EQ]; move: EQ f =>-> f H {T}.
    rewrite -(Eqdep_dec.inj_pair2_eq_dec _ _ _ _ _ _ H) => {H};
      last by move=>x y; apply/(decP eqP).
    by move=>[<-] pl; apply: (of_wt_proc (app f pl)).
  - by move=> H1 H2; apply: Ih; [apply: H1 | apply: H2].
Qed.
Arguments to_alts_wt [_] _.

(* Well-typed recv *)
Definition wt_recv Ls (p : role) (a : wt_alts Ls)
  : wt_proc (l_msg l_recv p Ls)
  := exist _ _ (t_Recv p (same_dom_alts a) (to_alts_wt a)).

Definition sing_alt L1 (a : wt_alt L1) : wt_alts [:: L1]
  := wta_sing a.
Definition cons_alt L1 Ls (a : wt_alt L1) (alts : wt_alts Ls)
  : wt_alts (L1 :: Ls) := wta_cons a alts.

Print wt_alt.
Declare Scope proc_scope.
Notation " \lbl l1 , x ':' T1 ; p1"
  := (@wt_cont l1 T1 _ (fun x => p1))
       (at level 0, x ident, p1 constr at level 200) : proc_scope.

Notation "[ 'alts' | a1 | .. | a2 | an ]"
  := (cons_alt a1 .. (cons_alt a2 (sing_alt an)) .. )
       (at level 0,
        a1 constr at level 200,
        a2 constr at level 200,
        an constr at level 200) : proc_scope.

Notation "\branch" := (wt_recv) (at level 0) : proc_scope.
Notation "\recv" := (fun p a => let: a' := sing_alt a in wt_recv p a')
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

Inductive sel_alt : (lbl * (mty * l_ty)) -> Type :=
| if_alt (b : bool) (l : lbl)  T (pl : coq_ty T) L (P : wt_proc L)
  : sel_alt (l, (T, L))
| df_alt (l : lbl) T (pl : coq_ty T) L (P : wt_proc L)
  : sel_alt (l, (T, L))
| sk_alt (l : lbl) (T : mty) (L : l_ty)
  : sel_alt (l, (T, L))
.

Inductive sel_alts : seq (lbl * (mty * l_ty)) -> Type :=
| sa_nil L : sel_alt L -> sel_alts [:: L]
| sa_cons L Ls : sel_alt L -> sel_alts Ls -> sel_alts (L :: Ls).

Notation "'\case' b '=>' l ',' pl '\as' T '!' P"
  := (if_alt b l (T:=T) pl P)
       (at level 0, P constr at level 200) : proc_scope.
Notation " '\otherwise' '=>' l , pl '\as' T '!' P"
  := (df_alt l (T:=T) pl P) (at level 0, P constr at level 200)
     : proc_scope.
Notation "'\skip' '=>' l , pl '!' P"
  := (sk_alt l pl P) (at level 0, P constr at level 200)
     : proc_scope.
Notation "[ 'sel' '|' a1 '|' .. '|' a2 '|' an ]"
  := (sa_cons a1 .. (sa_cons a2 (sa_nil an)) .. )
       (at level 0,
        a1 constr at level 200,
        an constr at level 200) : proc_scope.

Definition is_dflt L (s : sel_alt L ) :=
  match s with
  | df_alt _ _ _ _ _ => true
  | _ => false
  end.

Definition is_skip L (s : sel_alt L) :=
  match s with
  | sk_alt _ _ _ => true
  | _ => false
  end.

Fixpoint all_alts (P : forall L, sel_alt L -> bool) Ls (a : sel_alts Ls) : bool
  := match a with
     | sa_nil _ h => P _ h
     | sa_cons _ _ h t => P _ h && all_alts P t
     end.

Fixpoint has_single_default Ls (s : sel_alts Ls) :=
  match s with
  | sa_nil _ h => is_dflt h
  | sa_cons _ _ h t => if is_dflt h then all_alts is_skip t
                       else has_single_default t
  end.

Lemma hsd_if_false b l T (c : coq_ty T) L (w : wt_proc L)
  : ~ has_single_default (sa_nil (if_alt b l c w)).
Proof. by []. Qed.

Lemma hsd_sk_false l T L
  : ~ has_single_default (sa_nil (sk_alt l T L)).
Proof. by []. Qed.

About wt_sel.

Lemma hsd_cons_next L Ls (h : sel_alt L) (t : sel_alts Ls)
  : has_single_default (sa_cons h t) -> ~~ (is_dflt h) -> has_single_default t.
Proof. by case: h. Qed.

Lemma ul_next h t : unique_labels (h :: t) -> unique_labels t.
Proof. by move=>/andP-[]. Qed.

Fixpoint wt_select p Ls (s : sel_alts Ls)
  : has_single_default s ->
    unique_labels Ls ->
    wt_proc (l_msg l_send p Ls)
  := match s with
     | sa_nil L h =>
       match h
             in sel_alt L
             return
             has_single_default (sa_nil h) ->
             unique_labels [:: L] ->
             wt_proc (l_msg l_send p [:: L])
       with
       | sk_alt _ _ _ => fun H=> match hsd_sk_false H with end
       | if_alt _ _ _ _ _ _ => fun H=> match hsd_if_false H with end
       | df_alt l _ v _ k => fun H0 H1 => wt_send p l v k
       end
     | sa_cons L Ls h t =>
       match h
             in sel_alt L
             return
             has_single_default (sa_cons h t) ->
             unique_labels (L :: Ls) ->
             wt_proc (l_msg l_send p (L :: Ls))
       with
       | sk_alt l T L =>
         fun H1 H2 =>
           sel_skipL p [:: (l, (T, L))]
                  (@wt_select p Ls t (hsd_cons_next H1 is_true_true)
                              (ul_next H2)) H2
       | if_alt b l _ v _ k =>
         fun H1 H2 =>
           wt_sel b (wt_send p l v k)
                  (@wt_select p Ls t (hsd_cons_next H1 is_true_true)
                              (ul_next H2)) H2
       | df_alt l _ v _ k => fun _ H2 => sel_skipR p Ls (wt_send p l v k) H2
       end
     end.

Notation "'\select' p a" := (@wt_select p _ a is_true_true is_true_true)
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

Fixpoint ping_pong_client3 n p {struct n}:=
  match n with
  | 0 =>
    [proc \select p
          [sel
          | \otherwise => Bye, tt \as T_unit ! finish
          | \skip => Ping, T_nat !
                                 l_msg l_recv p
                                 [:: (Pong, (T_nat, projT1 (ping_pong_client1 p)))]]
    ]
  | m.+1 =>
    [proc \select p
          [sel
          | \skip => Bye, T_unit ! l_end
          | \otherwise =>
            Ping, n \as T_nat !
              (\recv p \lbl Pong, x : T_nat; projT2 (ping_pong_client3 m p))
          ]
    ]
  end.

Fixpoint l_unravel_n n L :=
  match n, lunroll (lrec_depth L) L with
  | n.+1, l_msg p q Ks => l_msg p q [seq (K.1, (K.2.1, l_unravel_n n K.2.2)) | K <- Ks]
  | _, _ => L
  end.

Goal projT1 (ping_pong_client3 4 p) = l_unravel_n 9 (projT1 (ping_pong_client1 p)).
  by [].
Qed.


Definition ping_pong_client4 p :=
  [proc \select p
        [sel
        | \skip => Bye, T_unit ! l_end
        | \otherwise => Ping, 1 \as T_nat !
              loop(
                \recv p \lbl Pong, x : T_nat;
                  \select p
                   [sel
                   | \case (x > 3) => Bye, tt \as T_unit ! finish
                   | \otherwise => Ping, x + 1 \as T_nat ! jump 0
                   ]
              )
        ]
  ].
Eval compute in projT1 (ping_pong_client4 p).
Eval compute in get_proc (projT2 (ping_pong_client4 p)).

Goal forall Li Lc, (Li = projT1 (ping_pong_client4 p) /\
                    Lc = l_expand (projT1 (ping_pong_client1 p))) ->
                   LUnroll Li Lc.
  apply/paco2_acc=> r _ /(_ _ _ (conj erefl erefl))/=-CIH Li Lr [->->].
  apply: paco2_fold; rewrite l_expand_once/=; constructor=>/=;
    first by apply/same_dom_eta/same_dom_extend/same_dom_extend/same_dom_refl.
  move=> l Ty G G'; rewrite /extend/empty/=.
  case: ifP=>//;
    first by move=>_ [<-<-] [<-]; left; apply/paco2_fold;
             rewrite l_expand_once; constructor.
  case: ifP=>//; move=> _ _ [<-<-] [<-]; left; apply/paco2_fold.
  constructor=>/=; left; rewrite l_expand_once/=.
  apply: paco2_fold; constructor;
    first by apply/same_dom_eta/same_dom_extend/same_dom_refl.
  move=> {}l {}Ty {}G {}G'/=; rewrite /extend/empty/=.
  by case: ifP=>// _ [<-<-] [<-]; right; apply/CIH.
Qed.

Close Scope proc_scope.

End Examples.
