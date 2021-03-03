(* Tutorial *)

From mathcomp Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

Require Import Extraction.

From Paco Require Import paco paco2.

Require Import MPST.Common.
Require Import MPST.Global.
Require Import MPST.Projection.
Require Import MPST.Local.
Require Import MPST.TraceEquiv.
Require Import MPST.Proc.
Require Import MPST.Zooid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Open Scope proc_scope.


(*
 * PingPong Example
 *)

Definition Bye := 0.
Definition Ping := 1.
Definition Pong := 1.

Definition pp_server := 0.
Definition pp_client := 1.

Definition ping_pong :=
  g_rec (
      g_msg pp_client pp_server
            [::
               (Bye, (T_unit, g_end));
               (Ping,
                (T_nat,
                 g_msg pp_server pp_client [:: (Pong, (T_nat, g_var 0))]))
            ]
    ).

Definition pp_env := \project ping_pong.
Definition pp_server_lt := \get pp_env pp_server.
Definition pp_client_lt := \get pp_env pp_client.

Definition ping_pong_server : wt_proc pp_server_lt :=
     loop (
       \branch pp_client
        [alts
        | \lbl Bye, _ : T_unit;
            finish
        | \lbl Ping, x : T_nat;
            (\send pp_client Pong x (jump 0))
        ]
     ).


Definition to_proc p := get_proc (projT2 p).

Lemma pp_s1 : of_lt_unr pp_server (get_proc ping_pong_server) pp_env.
Proof.
  exists pp_server_lt;split=>//.
  apply: (projT2 ping_pong_server).
  by apply: l_expand_unr.
Qed.


Definition ping_pong_client0 : wt_proc pp_client_lt :=
     loop (
       \select pp_server
        [sel
        | \otherwise => Bye, tt \as T_unit ! finish
        | \skip => Ping, T_nat ! l_msg l_recv pp_server [:: (Pong, (T_nat, l_var 0))]

        ]
     ).


Lemma pp_c0 : of_lt_unr pp_client (get_proc ping_pong_client0) pp_env.
Proof.
  exists pp_client_lt; split.
  - by apply: (projT2 ping_pong_client0).
  - by apply: l_expand_unr.
Qed.

Definition ping_pong_client1 : wt_proc pp_client_lt :=
     loop (
       \select pp_server
        [sel
        | \skip      => Bye , T_unit ! l_end
        | \otherwise => Ping, 1 \as T_nat !
              (\recv pp_server \lbl Pong, x : T_nat; (jump 0))
        ]
     ).

Lemma pp_c1 : of_lt_unr pp_client (get_proc ping_pong_client1) pp_env.
Proof.
  exists pp_client_lt; split.
  - by apply: (projT2 ping_pong_client1).
  - by apply: l_expand_unr.
Qed.

Definition ping_pong_client2 :=
  [proc
     \select pp_server
     [sel
     | \otherwise => Bye, tt \as T_unit ! finish
     | \skip => Ping, T_nat !
             l_msg l_recv pp_server
             [:: (Pong, (T_nat, pp_client_lt))]
     ]
  ].


Lemma pp_c2 : of_lt_unr pp_client (to_proc ping_pong_client2) pp_env.
Proof.
  exists (projT1 ping_pong_client2); split.
  - by apply: (projT2 (projT2 ping_pong_client2)).
  - rewrite -[projT1 ping_pong_client2]/(lunroll 1 pp_client_lt).
    by rewrite -LUnroll_ind; apply: l_expand_unr.
Qed.


Fixpoint ping_pong_client3 n {struct n}:=
  match n with
  | 0 =>
    [proc \select pp_server
          [sel
          | \otherwise => Bye, tt \as T_unit ! finish
          | \skip => Ping, T_nat !
                                 l_msg l_recv pp_server
                                 [:: (Pong, (T_nat, pp_client_lt))]]
    ]
  | m.+1 =>
    [proc \select pp_server
          [sel
          | \skip => Bye, T_unit ! l_end
          | \otherwise =>
            Ping, n \as T_nat !
              (\recv pp_server \lbl Pong, x : T_nat; projT2 (ping_pong_client3 m))
          ]
    ]
  end.

Fixpoint l_unravel_n n L :=
  match n, lunroll (lrec_depth L) L with
  | n.+1, l_msg p q Ks => l_msg p q [seq (K.1, (K.2.1, l_unravel_n n K.2.2)) | K <- Ks]
  | _, _ => L
  end.

Goal projT1 (ping_pong_client3 0) = l_unravel_n 1 pp_client_lt.
    by [].
Qed.


Definition ping_pong_client4 :=
  [proc \select pp_server
        [sel
        | \skip => Bye, T_unit ! l_end
        | \otherwise => Ping, 1 \as T_nat !
              loop(
                \recv pp_server \lbl Pong, x : T_nat;
                  \select pp_server
                   [sel
                   | \case (x > 3) => Bye, tt \as T_unit ! finish
                   | \otherwise => Ping, x + 1 \as T_nat ! jump 0
                   ]
              )
        ]
  ].
Definition ppc4_t1 := Eval compute in projT1 ping_pong_client4.
Definition ppc4_t2 := Eval compute in get_proc (projT2 ping_pong_client4).

Goal forall Li Lc, (Li = projT1 ping_pong_client4 /\
                    Lc = l_expand pp_client_lt) ->
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
