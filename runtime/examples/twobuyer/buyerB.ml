open GeneratedLib.Code
open Comm

let buyerA = 0
let buyerB = 1
let seller = 2

let participants = [
    { role_to = seller
    ; spec = Client(build_addr "127.0.0.1" 10002)
    }
  ; { role_to = buyerA
    ; spec = Client(build_addr "127.0.0.1" 10003)
  }]

let () = print_endline "Implementation for the role of the buyer B in twobuyer"
       ; if Log.create_log "buyer_b" then print_endline "Logging." else ()
       ; execute_extracted_process participants (module BUYERB)
