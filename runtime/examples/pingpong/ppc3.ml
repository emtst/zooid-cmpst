open GeneratedLib.Code
open Comm

let pp_server = 0
let pp_client = 1

let participants = [
    { role_to = pp_server
    ; spec = Client(build_addr "127.0.0.1" 10201)
  }]

let () = print_endline "Implementation for the role of the client in pingpong"
       ; if Log.create_log "ppc3" then print_endline "Logging." else ()
       ; execute_extracted_process participants (module PPCLIENT3)
