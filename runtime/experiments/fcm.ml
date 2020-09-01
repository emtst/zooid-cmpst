(* Playing with first class modules *)

module type TEST =
  sig
    val f : int -> int
  end

module Test : TEST =
  struct
    let f x = x
  end


module type FUNCTOR_RESULT =
  sig
    val result : int
  end

module type TEST_FUNCTOR =
  functor (T : TEST) -> FUNCTOR_RESULT


module TestFunctor (T : TEST) =
  struct
    let result = T.f 8
  end

let real_f (x : int) : (module TEST) = (module Test)

let real_f' (x : int) : (module TEST) =
  (module struct
    let f y = x + y
   end)

let six = let (module M) = real_f' 5 in M.f 1


let test_functor =
  let m = real_f' 5 in
  let (module M : TEST) = m in
  let (module F : FUNCTOR_RESULT) = (module TestFunctor(M)) in
  string_of_int F.result |> print_endline
