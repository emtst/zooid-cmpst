
open Datatypes


let ask_user () =
  print_endline "Enter: 'a' for adding, 'q' for quitting";
  let inp = read_line () in
  if inp = "a" then
    let n1 = print_string "Enter a first summand: " ; read_int () in
    let n2 = print_string "Enter a second summand: " ; read_int () in
    Coq_inl (n1, n2)
  else
    Coq_inr ()

let print_nat n =
  print_string @@ "Result: " ^ string_of_int n ^ "\n"
