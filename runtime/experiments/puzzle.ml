(* new experiment *)

(* a module and a function that builds it *)
module type PAR = sig
  type t
  val x : t
end

let build_with_string (foo : string) : (module PAR) =
  (module struct
     type t = string
     let x = foo
   end)


(* a functor and its type *)
module type FUNC =
  functor (P : PAR) -> sig
    module P : PAR
    val id : P.t -> P.t
  end

module Func : FUNC =
  functor (P: PAR) -> struct
    module P = P
    let id x = x
  end

module type RES = sig
  module P : PAR
  val id : P.t -> P.t
end

(* the problem: instantiate the functor with the result of the function *)
let test_func_par =
  let (module Par) = build_with_string "foo" in
  let _x = (module Func(Par): RES) in
  ()
