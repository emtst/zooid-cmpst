(* Playing with first class modules *)

module type TEST =
  sig
    val f : int -> int
  end

module Test : TEST =
  struct
    let f x = x
  end

let real_f (x : int) : (module TEST) = (module Test)

let real_f' (x : int) : (module TEST) =
  (module struct
    let f y = x + y
   end)

let six = let (module M) = real_f' 5 in M.f 1
