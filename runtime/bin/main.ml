(* Main file *)
open Unix

let get_my_addresses () =
  let hi = gethostname () |> gethostbyname in
  hi.h_addr_list |> Array.to_list

let () =
  print_endline "Zooid runtime info helper (only provides your IP addresses)" ;
  let addrs = get_my_addresses () |> List.map string_of_inet_addr in
  "Host: " ^ gethostname () ^ " IPs: " ^ String.concat ", " addrs |> print_endline
