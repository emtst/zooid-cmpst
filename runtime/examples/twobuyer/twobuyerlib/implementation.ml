


let read_item : int = Random.int 3

let print_quote x =
  "The book price is: £ " ^ string_of_int x |> print_endline

let read_proposal () =
  print_endline "Enter your offer (int): " ;
  read_int ()


let sold () = print_endline "Congratulations on your new book!"

let notsold () = print_endline "Sorry it did not work out, next time!"
