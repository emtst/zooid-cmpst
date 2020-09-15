open PipelineLib.Code
open Comm

let ralice = 0
let rbob = 1
let rcarol = 2

let participants = [
    { role_from = ralice
    ; role_to = rbob
    ; spec =   Server(build_addr "127.0.0.1" 10001)
  }]

let () = print_endline "Implementation for the role of alice in the pipeline"
       ; if Log.create_log "alice" then print_endline "Logging." else ()
       ; Common.execute_process participants (module ALICE)
