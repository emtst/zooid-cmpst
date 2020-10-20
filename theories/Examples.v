(* examples *)

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
Let p : role := 0.
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

Definition test1_t1 := Eval compute in fun b1 b2 => projT1 (test1 b1 b2).
Definition test1_t2 := Eval compute in fun b1 b2 => get_proc (projT2 (test1 b1 b2)).

Definition test : typed_proc
  := [proc
        \branch p
        [alts
        | \lbl 0, x : T_bool; if x then wt_end else wt_end
        | \lbl 1, x : T_nat ; wt_end
        ]
     ].
Definition test_t1 := Eval compute in projT1 test.
Definition test_t2 := Eval compute in get_proc (projT2 test).

(*** PING PONG protocols
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


(*** Two-buyer protocol
 *)

(**
 * Message labels
 *)
Definition BookId := 0.
Definition Quote := 1.
Definition ProposeA := 2.
Definition Buy := 3.
Definition Cancel := 4.
Definition Date := 5.

(**
 * Participants
 *)

Definition BuyerA := 0.
Definition BuyerB := 1.
Definition Seller := 2.

Definition two_buyer :=
  g_msg
    BuyerA Seller
    [:: (BookId,
         (T_nat,
          g_msg
            Seller BuyerA
            [:: (Quote,
                 (T_nat,
                  g_msg
                    Seller BuyerB
                    [:: (Quote,
                         (T_nat,
                          g_msg
                            BuyerA BuyerB
                            [:: (ProposeA,
                                 (T_nat,
                                  g_msg
                                    BuyerB Seller
                                    [:: (Buy,
                                         (T_nat,
                                          g_msg Seller BuyerB
                                                [:: (Date, (T_nat, g_end))]
                                        ));
                                        (Cancel, (T_unit, g_end))
                                    ]
                                ))
                            ]
                        ))
                    ]
                ))
            ]
        ))
    ].

Definition twob_env := \project two_buyer.
Definition twob_seller_lt := \get twob_env Seller.
Definition twob_buyA_lt := \get twob_env BuyerA.
Definition twob_buyB_lt := \get twob_env BuyerB.

(* Eval compute in twob_seller_lt. *)

Definition ItemTable i :=
  match i with
  | 0 => 300
  | 1 => 50
  | 2 => 75
  | _ => 0
  end.

Definition AvailableDate i :=
  match i with
  | 0 => 3
  | 1 => 1
  | 2 => 10
  | _ => 0
  end.

Parameter read_item : coq_ty T_nat.
Extract Constant read_item => "TwoBuyerLib.Implementation.read_item".

Definition seller_proc : wt_proc twob_seller_lt :=
     \recv BuyerA \lbl BookId, x : T_nat;
     \send BuyerA Quote (T:=T_nat) (ItemTable x) (
     \send BuyerB Quote (T:=T_nat) (ItemTable x) (
     \branch BuyerB
      [alts
      | \lbl Buy, y : T_nat; \send BuyerB Date (T:=T_nat )(AvailableDate x) finish
      | \lbl Cancel, x : T_unit; finish
      ]
  )).

Parameter print_quote : coq_ty T_nat -> unit.
Parameter read_proposal : unit -> coq_ty T_nat.

Extract Constant print_quote => "TwoBuyerLib.Implementation.print_quote".
Extract Constant read_proposal => "TwoBuyerLib.Implementation.read_proposal".

Definition buyerA : wt_proc twob_buyA_lt :=
     \send Seller BookId (T:=T_nat) read_item (
     \recv Seller \lbl Quote, x : T_nat;
       toCtx print_quote x (
               readFromEnv read_proposal (fun proposal =>
               \send BuyerB ProposeA (T:=T_nat) proposal
          finish)
      )
  ).


Definition buyerB : wt_proc twob_buyB_lt :=
     \recv Seller \lbl Quote, x : T_nat;
     \recv BuyerA \lbl ProposeA, y : T_nat;
     \select Seller
      [sel
      | \case y >= divn x 3
        => Buy, (x - y) \as T_nat ! \recv Seller \lbl Date, x : T_nat; finish
      | \otherwise
        => Cancel, tt \as T_unit! finish
      ].

(* Pipeline example *)

Definition Alice := 0. Opaque Alice.
Definition Bob := 1. Opaque Bob.
Definition Carol := 2. Opaque Carol.

Definition Lbl := 1. Opaque Lbl.

Definition pipe :=
  g_rec
    (g_msg Alice Bob
        [:: (Lbl, (T_nat,
                   g_msg Bob Carol
                         [:: (Lbl, (T_nat, g_var 0))]))]).

Definition pipe_env := \project pipe.
Definition pp_alice_lt := \get pipe_env Alice.
Definition pp_bob_lt := \get pipe_env Bob.
Definition pp_carol_lt := \get pipe_env Carol.

Definition alice : wt_proc pp_alice_lt :=
     loop (
          \send Bob Lbl (T:=T_nat) 3 (jump 0)
       ).

Definition bob : wt_proc pp_bob_lt :=
     loop (
       \recv Alice \lbl Lbl, x : T_nat;
       \send Carol Lbl (T:= T_nat) (x * 2) (jump 0)
     ).

Definition carol : wt_proc pp_carol_lt :=
     loop (
       \recv Bob \lbl Lbl, x : T_nat;
        (jump 0)
     ).


(* Calculator example from FluidSession/blob/dev/Adder/Adder.scr *)

(* roles for calculator's client and server *)
Definition AC := 0. Opaque AC.
Definition AS := 1. Opaque AS.

(* labels *)
Definition AHello := 1. Opaque AHello.
Definition AAdd := 2. Opaque AAdd.
Definition ARes := 3. Opaque ARes.
Definition ABye := 4. Opaque ABye.

(* the global type for the calculator *)
Definition calculator :=
  g_rec
    (g_msg AC AS
           [:: (AHello, (T_unit,
                        g_msg AC AS
                              [:: (AAdd, (T_nat,
                                         g_msg AC AS [:: (AAdd, (T_nat,
                                                                g_msg AS AC [:: (ARes, (T_nat, g_var 0))]))]));
                                  (ABye, (T_unit, g_msg AS AC [:: (ABye, (T_unit, g_end))]))]))]).

(* project all the roles *)

(* note that if the definition typechecks then it is well formed.
There's no need for option types or error checking above what Coq
provides *)
Definition calculator_env := \project calculator.

Definition calculator_client_lt := \get calculator_env AC.
Definition calculator_server_lt := \get calculator_env AS.

(* non-interactive implementation *)

Definition AServer0 : wt_proc calculator_server_lt :=
  loop (
      \recv AC \lbl AHello, _ : T_unit ;
      \branch AC
       [alts
       | \lbl AAdd, x : T_nat ;
         \recv AC \lbl AAdd, y : T_nat ; \send AC ARes (T := T_nat) (x + y) (jump 0)
       | \lbl ABye, _ : T_unit ; \send AC ABye (T := T_unit) tt finish
       ]
    ).

Definition AClient0 : wt_proc calculator_client_lt :=
  loop (
      \send AS AHello (T := T_unit) tt
    \select AS
     [sel
     | \otherwise => AAdd, 2 \as T_nat ! \send AS AAdd (T := T_nat) 2 (\recv AS \lbl ARes, _ : T_nat ; jump 0)
     | \skip => ABye, _ ! _
     ]
    )
.

(* interactive implementation *)



Definition user_interaction := coq_ty (T_sum (T_prod T_nat T_nat) T_unit).

Parameter ask_user : unit -> user_interaction.
Parameter print_nat : coq_ty T_nat -> unit.

Extract Constant ask_user => "Calculator.ask_user".
Extract Constant print_nat => "Calculator.print_nat".


Definition quit (ui : user_interaction) :  bool :=
  match ui with
  | inl _ => false
  | inr _ => true
  end.

Definition adding (ui : user_interaction) :  bool := negb (quit ui).
Definition get_fst(ui : user_interaction) : nat :=
  match ui with
  | inl (x, _) => x
  | inr _ => 0
  end.
Definition get_snd(ui : user_interaction) : nat :=
  match ui with
  | inl (_, x) => x
  | inr _ => 0
  end.

Definition AServer : wt_proc calculator_server_lt :=
  loop (
      \recv AC \lbl AHello, _ : T_unit ;
      \branch AC
       [alts
       | \lbl AAdd, x : T_nat ;
         \recv AC \lbl AAdd, y : T_nat ; \send AC ARes (T := T_nat) (x + y) (jump 0)
       | \lbl ABye, _ : T_unit ; \send AC ABye (T := T_unit) tt finish
       ]
    ).

Definition AClient : wt_proc calculator_client_lt :=
  loop (
      \send AS AHello (T := T_unit) tt
       (readFromEnv ask_user
                (fun au =>
                   \select AS
                    [sel
                    | \case (adding au) => AAdd, (get_fst au) \as T_nat ! \send AS AAdd (T := T_nat) (get_snd au) (\recv AS \lbl ARes, n : T_nat ; toCtx print_nat n (jump 0))
                    | \otherwise => ABye, tt \as T_unit ! \recv AS \lbl ABye, _ : T_unit ; finish
                    ]
                )
       )
    )
.

Definition AClient' : wt_proc calculator_client_lt :=
  loop (
      \send AS AHello (T := T_unit) tt
       (readFromEnv ask_user
                (fun aoe =>
                   \select AS
                    [sel
                    | \case (adding aoe) => AAdd, aoe \as T_nat ! \send AS AAdd (T := T_nat) 2 (\recv AS \lbl ARes, n : T_nat ; toCtx print_nat n (jump 0))
                    | \otherwise => ABye, tt \as T_unit ! \recv AS \lbl ABye, _ : T_unit ; finish
                    ]
                )
       )
    )
.

Close Scope proc_scope.
