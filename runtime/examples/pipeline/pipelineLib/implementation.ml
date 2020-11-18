



let get_input () =
  print_string "Enter the namber to put into the pipeline:" ; read_int ()

let compute x = x * 2

let print n = print_endline @@ "The result is: " ^ string_of_int n
