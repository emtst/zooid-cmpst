open GeneratedLib.Code
open Comm

let buyerA = 0
let buyerB = 1
let seller = 2

let participants = [
    { role_to = buyerA
    ; spec = Server(build_addr "127.0.0.1" 10001)
    }
  ; { role_to = buyerB
    ; spec = Server(build_addr "127.0.0.1" 10002)
  }]

let () = print_endline "Implementation for the role of the seller in twobuyer"
       ; if Log.create_log "seller" then print_endline "Logging." else ()
       ; execute_extracted_process participants (module SELLER)
