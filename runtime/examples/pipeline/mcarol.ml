open GeneratedLib.Code
open Comm

let ralice = 0
let rbob = 1
let rcarol = 2

let participants = [
    { role_to = rbob
    ; spec =   Client(build_addr "127.0.0.1" 10302)
  }]


let () = print_endline "Implementation for the role of carol in the pipeline"
       ; if Log.create_log "carol" then print_endline "Logging." else ()
       ; execute_extracted_process participants (module CAROL)
