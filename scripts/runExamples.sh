#!/bin/bash

if [ ! -d "scripts" ]; then
    cd ..
fi

./scripts/buildAll.sh > /dev/null

cat <<WELCOME

Zooid tutoria & code walk-through
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To make the most of this tutorial please follow along with a copy of
the Zooid repository and your favourite editor.

We will now interactively present and run some of the examples in the
system.

We will run the examples in the following order:
1- a simple calculator example
2- a pipeline computation protocol between three participants
3- the classical MPST protocol for two buyers

(press enter to start running the examples)
WELCOME

read -r input ; clear

cat<<CALCULATORINTRO

** CALCULATOR PROTOCOL **

The first example is a binary protocol, this example will walk you
through an implementation of a protocol in Zooid.

The calculator protocol defines a server and client, where the client
greets the server with the 'AHello' msg. Then sends either the
operation, operands and receives the result and repeats (messages
'AAdd' and 'ARes') or finishes the interaction (message 'ABye').

First of all, the protocol definition and the process implementation
is done in Coq. In this case the code is present in the file:

  theories/Examples.v

in the Zooid repository.

We will refer to the main Coq definitions used to implemet the server and in the client.

| Definition           | Description                                      |
+----------------------+--------------------------------------------------+
| calculator           | this defines the global type for the server      |
|                      | and the client                                   |
+----------------------+--------------------------------------------------+
| calculator_client_lt | this defines the local projection for the client |
+----------------------+--------------------------------------------------+
| calculator_server_lt | this defines the local projection for the server |
+----------------------+--------------------------------------------------+
| ask_user             | These are the actions that provide the UI.       |
| print_nat            | These actions are implemented in OCaml as we will|
|                      | see later.                                       |
+----------------------+--------------------------------------------------+
| AServer              | The process that implements the server role      |
| AClient              | The process that implements the client role      |
+----------------------+--------------------------------------------------+

(press enter to continue)
CALCULATORINTRO

read -r input ; clear

cat<<RUNTIME

Zooid programs are transport agnostic, the implementation of the
proper transport in OCAml is deferred to the user. In our examples, we
provide a TCP/IP implementation built on top of the LWT library
(https://ocsigen.org/lwt). This code is all in the file:

  runtime/lib/comm.ml

The implementation of the UI and OCaml parts of the calculator example
are in:

  runtime/examples/calculator/calcsvr.ml
  runtime/examples/calculator/calcc.ml
  runtime/examples/caclculator/calculatorlib/calculator.ml

In the next section we will discuss the implementation of the server
entry point (the client is analogous) and the UI library.

(press enter to continue)
RUNTIME

read -r input ; clear


cat<<SVRENTRY

The server entry point is the sever executable compiled by OCaml from
the extracted Zooid implementation.

Fundamentally, it is calling the function:

  execute_extracted_process

This function takes two parameters, the list of participants and the
extracted module that implements a process.

The participants defines the session providing addresses and ports for
all the participants this process interacts with. In this case, it is
just the client role. The code is below:

  let participants = [
      { role_to = client
      ; spec =   Server(build_addr "127.0.0.1" 10101)
    }]

Finally the Zooid code is invoked by:

  execute_extracted_process participants (module AServer)

That tells the runtime to behave like the module 'AServer' using the
channels specified in 'participants'.

(press enter to continue)
SVRENTRY

read -r input ; clear

cat<<CALCLIB

The final aspect of the calculator protocol is implementing the UI
methods that the Zooid implementation deferred to OCaml.

As mentioned before, these are in 'calculator.ml' file and they are
simply two functions:

  ask_user  -- this function prompts for two numbers in standard
               input and returns the pair of them.
  print_nat -- this function simply prints the result from the server
               an integer.

(press enter to continue)
CALCLIB

read -r input ; clear


cat<<ENDCALC

This concludes the walkthrough the code, we will now execute the
described code.

For simplicity we run them locally, but a distributed session can be
specified using the 'participants' datastructure in the process entry
points as described above.

Now you can have fun interacting with the calculator.

(press enter to continue)
ENDCALC

read -r input

./scripts/runCalculator.sh


cat<<INTERACTCALCEND

(press enter to continue)

INTERACTCALCEND
read -r input ; clear


cat<<INTROPIPE

** PIPELINE PROTOCOL **

For our second example, we will consider our first multiparty
protocol. Where 'Alice' provides a number to 'Bob' who computes some
arbitrarily complex value and sends the result to 'Carol'. Then whole
pipeline repeats itself.

Again, the protocol definition and process implementation is done in
Zooid embeded in the 'Examples.v' Coq file.

| Definition  | Description.                                              |
+-------------+-----------------------------------------------------------+
| pipe        | the global type for the pipeline protocol                 |
+-------------+-----------------------------------------------------------+
| pp_alice_lt | the projected local types for each participant            |
| pp_bob_lt   |                                                           |
| pp_carol_lt |                                                           |
+-------------+-----------------------------------------------------------+
| get_input   | as before, the UI (get_input, and print) and the          |
| compute     | computation function are deferred to OCaml code because.  |
| print       | they are not concerned with the communication structure.  |
+-------------+-----------------------------------------------------------+
| alice       | these are the three definitions for each of the processes |
| bob         |                                                           |
| carol       |                                                           |
+-------------+-----------------------------------------------------------+

(press enter to continue)

INTROPIPE
read -r input ; clear

cat<<PIPEOCAML

As before, we will have an executable per role, and a library of UI
functions.

  runtime/examples/pipeline/malice.ml
  runtime/examples/pipeline/mbob.ml
  runtime/examples/pipeline/mcarol.ml
  runtime/examples/pipeline/pipelineLib/implementation.ml

Where the the first three are the executables for the roles, and the
last one defines the UI (asking and printing for numbers in the
standard input and the complex computation taht bob does (in this
examples it doubles the number it gets as input).

'mbob.ml' is the first time in this tutorial that we see a participant
that interacts with more than one role. You should also observe the
use of the 'Server' and 'Client' constructors to define which role
connects to which, and how they are used on the other endpoints
('malice.ml' and 'mcarol.ml')

(press enter to continue)

PIPEOCAML
read -r input ; clear

cat<<PIPERUN

Now to execute the pipeline multiple times, instead of Alice asking
for number each iteration, we feed Alice with random numbers.


PIPERUN

trap ctrl_c INT

function ctrl_c() {
        echo "\nDone with the pipeline!"
}

./scripts/runPipeline.sh

trap "" INT

clear

cat<<TWOBUYERINTRO

** TWO BUYER PROTOCOL **

For the final example of this walkthrough, the classical example from
the multiparty session type literature, the two buyer protocol.

This protocol models two buyers ('BuyerA', and 'BuyerB' presumably two
friends, let's say) who want to buy a book and split the cost from a
third participant ('Seller').

To achieve this 'BuyerA' queries the server for the price of a book by
using the message 'BookId', then 'Seller' send the message 'Quote' to
both buyers. At this point 'BuyerA' sends a proposal (how much they
are willing to pay of the book) to 'BuyerB'. With this information
'BuyerB' either chooses to send 'Buy' to the 'Seller' or 'Cancel' if
the split was not agreeable.

(press enter to continue)
TWOBUYERINTRO
read -r input ; clear


cat<<TBCODE

As before, the following defintions in 'Examples.v' specify this protocol:

| Definition.    | Description.                                              |
+----------------+-----------------------------------------------------------+
| two_buyer      | the global type for the protocol                          |
+----------------+-----------------------------------------------------------+
| twob_seller_lt | the local types that result from projection               |
| twob_buyA_lt   |                                                           |
| twob_buyB_lt   |                                                           |
+----------------+-----------------------------------------------------------+
| read_item      | the external functions for querying the seller's database |
| print_quote    | and printing and reading the quote and proposal.          |
| read_proposal  |                                                           |
+----------------+-----------------------------------------------------------+
| seller_proc    | the process implementation for the seller, and the two    |
| buyerA         | buyers.                                                   |
| buyerB         |                                                           |
+----------------+-----------------------------------------------------------+

And, similar as before, the ocaml code supporting them is in the
files:

  runtime/examples/twobuyer/seller.ml
  runtime/examples/twobuyer/buyerA.ml
  runtime/examples/twobuyer/buyerB.ml
  runtime/examples/twobuyer/twobuyerlib/implementation.ml

(press enter to continue)
TBCODE
read -r input ; clear

cat<<TBRUN

To finish, lets observe a run of the protocol where the book is £75
and the split is just £30 for buyerA and £45 for buyerB. Perhaps they
were not really good friends.

(press enter to continue)

TBRUN

read -r input

./scripts/runTwoBuyer.sh


cat<<FIN

THE END

With this we finish the walkthrough/tutorial for the calculator,
pipeline and twobuyer examples.

Thanks for making it this far!!

FIN
