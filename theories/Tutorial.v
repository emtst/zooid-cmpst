(** * Zooid Tutorial/walkthrough *)
(** ** Introduction

This file contains a walkthrough/tutorial on how to write Zooid
specification and processes. For succinctness this tutorial assumes
familiarity with the Coq proof assistant, the OCaml programming
language, and the theory of multiparty session types.

For the complete code, the source of this file is available in the
Zooid distribution in the directory <<theories/Tutorial.v>>. After
reading the HTML version of this document, we encourage you to go
interactively over the file. This will allow you to modify and test
things, and moreover go over the proofs step by step. <<Tutorial.v>>
also contains extra theorems whose study would help the understanding
of the more complex proofs.

*)

(* begin hide *)
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

(* end hide *)

(** ** The protocol definition: a global type

In this tutorial we will explore a binary protocol for clarity of
presentation. The objective is to discuss progressively more complex
implementations to motivate how one may approach programming with
Zooid.

The Ping Pong protocol definition we use here correspond to the
intuition of it. Let's explore it in more detail.
*)

(** First we define a pair of identifiers for the two roles, we use
natural numbers to represent each participant. *)

Definition pp_server := 0. Definition pp_client := 1.

(** In this protocol, the server will wait for messages from the
client, the client will choose to either send a 'Ping' message and
wait for the 'Pong' response, and repeat, or it will choose to send
'Bye' to end the protocol.

For this purpose we define three message identifiers as labels of each
message. Again, labels are also reprsented by natural numbers.
 *)


Definition Bye := 0. Definition Ping := 1. Definition Pong := 1.

(**

At this point we are ready to specify the global type, we do explore
in a step by step manner, and provide the full global type in the end.


This protocol is recursive, and it repeats itself from the begining,
so the first constructor is [g_rec] insicating that the fix point
starts here.

[Definition ping_pong := g_rec ...]


Then the client has the choice of finishing the interaction or
requesting a ping. The constructor [g_msg] allows one to express this,
it takes the source and target of the message and a list of messages
and their payload type and continuations. In this case we leave the
continuations as ellipsis for now. The payload for the message [Bye]
is just unit since the interaction has finished and no more
information is required and the payload for [Ping] is a natural number
for the server.

[Definition ping_pong := g_rec (g_msg pp_client pp_server [:: (Bye,
  (T_unit, ...) (Ping, (T_nat, ...))]])]

When the client sends the [Bye] label then the continuation is simply
to end ([g_end]):

[Definition ping_pong := g_rec ( g_msg pp_client pp_server [:: (Bye,
  (T_unit, g_end)); (Ping, (T_nat, ... ).]])]

On the case of the [Ping] label the behaviour is to let the server
respond with the [Pong] label and another natural number [ g_msg
pp_server pp_client [:: (Pong, (T_nat, ...))])) ]]

So far our still incomplete definition looks like this:

[Definition ping_pong := g_rec ( g_msg pp_client pp_server [:: (Bye,
  (T_unit, g_end)); (Ping, (T_nat, g_msg pp_server pp_client [::
  (Pong, (T_nat, ...))])) ] ).]])]

After the [Pong] label, both the client and the server are ready to do
another run of the protocol. Zooid uses de-Bruijn indices for its
recursion variables (introduced by the [g_rec] constructor). Since
there is only one recursion constructor, we invke it with [g_var 0].

With this we have completely specified the communication protocol for
this example.

The global type for this protocol is:
 *)

Definition ping_pong :=
  g_rec ( g_msg pp_client pp_server
    [:: (Bye,  (T_unit, g_end));
        (Ping, (T_nat, g_msg pp_server pp_client
          [:: (Pong, (T_nat, g_var 0))]))]).


(**

Note: the global type specifies all the acceptable behaviours by the
client and server, yet implementations get to choose which labels to
send, and the policies regarding the payloads (in this case the
numbers sent back and forth in the ping pongs.

----
*)

(** ** The local types of the participants

The local types for each participants are derived automatically by the
certified implementations.

*)


Definition pp_env := \project ping_pong.
Definition pp_server_lt := \get pp_env pp_server.
Definition pp_client_lt := \get pp_env pp_client.

(** [pp_env] contains the types for all participants from which we get
the types of each role.

----*)


(** ** The process implementations

*** The implementation of the server

First, we will implement the server. The server is in a sense simpler
because it will implement all the behaviours since in this protocol
only the client has meaningful choices (i.e.: to ping or quit). As a
policy for the payloads this server will simple echo back the payload
of the [Ping] message.

First start with a definition of an intrinsically typed process
[wt_proc] of type [pp_server_lt].

[Definition ping_pong_server : wt_proc pp_server_lt :=..]

The protocol starts with a fix point, so the first (smart) constructor
should be [loop] to allow for the recursion to happen.

[Definition ping_pong_server : wt_proc pp_server_lt := loop ..]

Following the protocol, the server has to respond to the client's
choice, we do this with [\branch pp_client [alts | ... ]] where the
alternatives are either [Bye] carrying a unit or [Ping] carrying a
natural number: [ [alts | \lbl Bye, _ : T_unit; ... | \lbl Ping, x :
T_nat; ...] ]

The server quits if it receives [Bye] with the process smart
constructor [finish] and otherwise it sends back [Pong] with the same
value it received in variable [x].

[\send pp_client Pong x ...]

To repeat the loop, we use again de-bruijn indices and we jump back
with [jump 0].

The complete definition of the server is thus:
 *)

Definition ping_pong_server : wt_proc pp_server_lt :=
  loop ( \branch pp_client
         [alts | \lbl Bye, _ : T_unit; finish
               | \lbl Ping, x : T_nat; (\send pp_client Pong x (jump 0))] ).

(* begin hide *)

(* this definition simple projects the untyped term from the
intrinsically typed process *)

Definition to_proc p := get_proc (projT2 p).

(* This lemma is just to show that the untyped process also admits the
global type *)
Lemma pp_s1 : of_lt_unr pp_server (get_proc ping_pong_server) pp_env.
Proof. exists pp_server_lt;split=>//. apply: (projT2
ping_pong_server). by apply: l_expand_unr. Qed.

(* end hide *)


(** *** The first client -- Always be saying goodbye

This first client is the simplest possible one. I just always asks the
server to finish the interaction by sending [Bye].

*)

Definition ping_pong_client0 : wt_proc pp_client_lt :=
  loop (\select pp_server
         [sel | \otherwise => Bye, tt \as T_unit ! finish
              | \skip => Ping, T_nat !
                l_msg l_recv pp_server [:: (Pong, (T_nat, l_var 0))]
         ]).

(** In this client we use the [\select pp_server ...] construct to
make a choice, for this we need to offer a series of conditions that
if met they are executed, or skipping some parts of the protocol. The
skips are necessary to simplify arguing that the local type of the
process corresponds to the one inferred from the terms (i.e.: avoiding
this would lead to more proof obligations).

The selection arguments:
[ [sel | \otherwise => Bye, tt \as T_unit !...| \skip => Ping, T_nat !...] ]
has two branches [\otherwise] that is
always taken and [\skip] that says that this branch is never taken,
note that [\skip] is annotated with the type of the continuation that
is skipped.
 *)

(* begin hide *)
Lemma pp_c0 : of_lt_unr pp_client (get_proc ping_pong_client0) pp_env.
Proof.
exists pp_client_lt; split.
- by apply: (projT2 ping_pong_client0).
- by apply: l_expand_unr.
Qed.
(* end hide *)

(** *** The second client -- Always be pinging

This client is more interesting than the previous one, by always
choosing to ping and never terminating.

*)

Definition ping_pong_client1 : wt_proc pp_client_lt :=
  loop ( \select pp_server
         [sel | \skip => Bye , T_unit ! l_end
              | \otherwise => Ping, 1 \as T_nat !
                (\recv pp_server \lbl Pong, x : T_nat; (jump 0)) ] ).

(** The implementation of this client does not use new elements, it
simply uses the elements that we knew of in a different way. *)

(* begin hide *)
Lemma pp_c1 : of_lt_unr pp_client (get_proc ping_pong_client1) pp_env.
Proof.
exists pp_client_lt; split.
- by apply: (projT2 ping_pong_client1).
- by apply: l_expand_unr.
Qed.
(* end hide *)



(** *** The third client -- Always be pinging just one time

This client behaves by sending one ping and then terminating. Also,
until now, all the clients followed the structure of the type step by
step. What we mean, is that they all do first the [loop], and then
[\select], and so and so. In this case, since we only want to send one
[Ping] and then terminate with [Bye] we have avoided the [loop]
construct.

Here is the definition of the process:
*)

Definition ping_pong_client2 :=
  [proc \select pp_server
        [sel | \otherwise => Bye, tt \as T_unit ! finish
             | \skip => Ping, T_nat !
               l_msg l_recv pp_server [:: (Pong, (T_nat, pp_client_lt))] ] ].

(**

Things to notice:

- no type annotation, we use Coq's type inference to get the type of
  this Zooid program.

- instead of starting with [loop] we start the process with [[proc
  ...]] to signal to Coq that this is a Zooid implicitely typed
  process.

- instead of sending [Bye] after receiving [Pong] we call
  [pp_client_lt] (the process that always says bye) to terminate the
  execution of the protocol and not have to implement it again.

This implementation strategy is more versatile, allowing us to write
process that are not structurally folloing their type's shape.
However, the inferred type is not 'obviously' the same as expected,
because of some unfoldings. In order to fill that gap the following
lemma fills that gap by showing that the process admits the right type
([to_proc] extracts the untyped process from the intrinsically typed
one).
*)

Lemma pp_c2 : of_lt_unr pp_client (to_proc ping_pong_client2) pp_env.
Proof.
  exists (projT1 ping_pong_client2); split.
  - by apply: (projT2 (projT2 ping_pong_client2)).
  - rewrite -[projT1 ping_pong_client2]/(lunroll 1 pp_client_lt).
      by rewrite -LUnroll_ind;
      apply: l_expand_unr.
Qed.

(** The proof should be simple enough as it resorts unroll and unravel
the coinductive types. *)


(** *** The fourth client -- Always be useful

This client shows how to use Coq infrastructure in Zooid code taking
advantage of Zooid's nature a shallow embedding in Coq.

This version of the client is the n-ary version of the previous one,
and we compute that using Coq's [Fixpoint]

The first definition is a recursive function that computes the process
that sends [n] times [Ping]. *)

Fixpoint ping_pong_client3 n {struct n}:=
  match n with
  | 0 => [proc
            \select pp_server
            [sel | \otherwise => Bye, tt \as T_unit ! finish
             | \skip => Ping, T_nat !
                        l_msg l_recv pp_server
                          [:: (Pong, (T_nat, pp_client_lt))]] ]
  | m.+1 => [proc
               \select pp_server
               [sel | \skip =>
  Bye, T_unit ! l_end | \otherwise => Ping, n \as T_nat ! (\recv
  pp_server \lbl Pong, x : T_nat; projT2 (ping_pong_client3 m)) ] ]
  end.

(** This unravels the local type n times. *)
Fixpoint l_unravel_n n L :=
  match n, lunroll (lrec_depth L) L with
  | n.+1, l_msg p q Ks => l_msg p q [seq (K.1, (K.2.1, l_unravel_n n K.2.2)) | K <- Ks]
  | _, _ => L end.


(** This shows that it works for one unravelling. The general proof is
left as an excercise. *)
Goal projT1 (ping_pong_client3 0) = l_unravel_n 1 pp_client_lt.
    by [].
Qed.

(** *** The fifth client -- Always be willing to stop

This version of the process sends [Ping] until the [Pong] payload is
larger than 3.

The only new construct in this client is the the [\case] clause in
[\select] that allows for a condition to be specified to continue with
this branch or continue with the rest.

Spend some time convincing yourself that the implementatio behaves
like the previous description.

*)


Definition ping_pong_client4 :=
  [proc \select pp_server
        [sel | \skip => Bye, T_unit ! l_end
         | \otherwise => Ping, 1 \as T_nat !
           loop(\recv pp_server \lbl Pong, x : T_nat;
               \select pp_server
                [sel | \case (x > 3) => Bye, tt \as T_unit ! finish
                     | \otherwise => Ping, x + 1 \as T_nat ! jump 0])]].


(** By now you have read [ping_pong_client4] and you may be convinced
that it follows the protocol. However, given that the process is not
constructed to follow the exact structure of the local type, Coq is
also not convinced.

The following theorem shows that the inferred type [projT1
ping_pong_client4 ] and [pp_client_lt] are unrollings of eachother.
*)
Goal forall Li Lc, (Li = projT1 ping_pong_client4 /\
                    Lc = l_expand pp_client_lt) -> LUnroll Li Lc.
Proof.
  apply/paco2_acc=> r _ /(_ _ _ (conj erefl erefl))/=-CIH Li Lr [->->].
  apply: paco2_fold;
    rewrite l_expand_once/=; constructor=>/=; first by
      apply/same_dom_eta/same_dom_extend/same_dom_extend/same_dom_refl.
  move=> l Ty G G'; rewrite /extend/empty/=.
  case:
    ifP=>//; first by move=>_ [<-<-] [<-]; left;
      apply/paco2_fold; rewrite l_expand_once; constructor.
  case: ifP=>//; move=> _ _ [<-<-] [<-]; left; apply/paco2_fold.
  constructor=>/=; left; rewrite l_expand_once/=.
  apply: paco2_fold; constructor; first by
      apply/same_dom_eta/same_dom_extend/same_dom_refl.
  move=> {}l {}Ty {}G {}G'/=; rewrite
           /extend/empty/=.
    by case: ifP=>// _ [<-<-] [<-];
      right; apply/CIH.
Qed.

(** This proof is also about unfoling and aligning the two types, and
while it is a bit frutrating to do, it does not require great
insights. In the future, Zooid will provide tools to automate these
proofs as much as possible.

---- *)

(** ** Final words

This tutorial explores how to implement processes using Zooid. The
remaining aspects are how to extract the code, and for that we invite
you to check the <<theories/Code.v>> file where all the examples are
extracted. Finally, to connect to the OCaml, first use the interactive
example walkthrough by running <<./run.sh>> from the root directory of
the Zooid distribution/docker container that contains pointers and
explanation of all the important details.

_Thank you very much_ for your attention.

The Zooid team.
*)
