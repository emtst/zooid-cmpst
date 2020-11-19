open GeneratedLib.Code
open Comm

let svr = 1
let client = 0

let participants = [
    { role_to = svr
    ; spec =   Client(build_addr "127.0.0.1" 10101)
  }]

let () = print_endline "Implementation for the role of the server in the calculator"
       ; if Log.create_log "client'" then print_endline "Logging." else ()
       ; execute_extracted_process participants (module AClient')
