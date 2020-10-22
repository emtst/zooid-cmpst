



let get_input () =
  print_string "Enter the namber to put into the pipeline:" ; read_int ()

let set_input, compute =
  let state = ref 0 in
  let set n = state := n in
  let comp () = !state * 2 in
  set, comp

let print n = print_string @@ "The result is: " ^ string_of_int n
