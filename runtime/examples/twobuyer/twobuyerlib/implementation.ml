


let read_item : int = 7

let print_quote x =
  "The offer is: " ^ string_of_int x ^ "<<<<<<<" |> print_endline

let read_proposal () =
  print_endline "Enter your offer (int): " ;
  read_int ()
