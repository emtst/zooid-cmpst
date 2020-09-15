open PipelineLib.Code
open Comm

let ralice = 0
let rbob = 1
let rcarol = 2

let participants =
  [ { role_from = rbob
    ; role_to = ralice
    ; spec =   Client(build_addr "127.0.0.1" 10001)
    }
  ; { role_from = rbob
    ; role_to = rcarol
    ; spec =   Server(build_addr "127.0.0.1" 10002)
    }
  ]


let () = print_endline "here we will have the implementation of pipeline"
       (* ; if Log.create_log "Bob" then print_endline "Logging." else () *)
       ; Common.execute_process participants (module BOB)
