open GeneratedLib.Code
open Comm

let ralice = 0
let rbob = 1
let rcarol = 2

let participants =
  [ { role_to = ralice
    ; spec =   Client(build_addr "127.0.0.1" 10301)
    }
  ; { role_to = rcarol
    ; spec =   Server(build_addr "127.0.0.1" 10302)
    }
  ]

let () = print_endline "Implementation for the role of bob in the pipeline"
       ; if Log.create_log "bob" then print_endline "Logging." else ()
       ; execute_extracted_process participants (module BOB)
