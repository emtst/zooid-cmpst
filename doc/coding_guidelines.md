# Coding Guidelines

## Naming Conventions

1. Since this project extracts to OCaml code, the general idea is to
   keep names and conventions that do not look out of place in OCaml
   code.

2. We try to keep a hybrid approach for naming:
   2.1. Camel case (as in CamelCase) for the name of constructors.
   2.2. Snake case (as in snake_case) for the names of
   functions/types/lemmas. Note that snake case names do not contain
   capitals.


## Proof Structure

1. Try to minimise the nesting of goals. The strategies to achieve
   this could be: add lemmas to move some parts out, or you can do
   some rewriting intially (e.g: splitting goals with two tactics
   using ";" ) that decomposes all the lemmas in top level lemmas.

2. Use "{ }" to structure the goals in lemmas and theorems. Ideally,
   this should be used only for the first level goals. If there are
   further goals you may decide to use +/- to structure the sub-proof.
   Use your "MRG common sense" to decide when to break this rule.

## Indentation

To be determined...
