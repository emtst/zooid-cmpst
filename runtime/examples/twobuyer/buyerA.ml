open GeneratedLib.Code
open Comm

let buyerA = 0
let buyerB = 1
let seller = 2

let participants = [
    { role_to = seller
    ; spec = Client(build_addr "127.0.0.1" 10401)
    }
  ; { role_to = buyerB
    ; spec = Server(build_addr "127.0.0.1" 10403)
  }]

let () = print_endline "Implementation for the role of the buyer A in twobuyer"
       ; if Log.create_log "buyer_a" then print_endline "Logging." else ()
       ; execute_extracted_process participants (module BUYERA)
