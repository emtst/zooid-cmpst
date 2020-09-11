open PipelineLib.Code

open Lwt.Infix
open Comm

module type PROCESS =
  sig
    module PM : PipelineLib.Proc.ProcessMonad
    val proc : unit PM.t
end

let experiment (participants : Comm.conn_desc list) : unit Lwt.t =
  Comm.build_participant participants >>= fun mp ->
  let (module IMP) = mp in
  let (module Proc) = (module BOB (IMP) : PROCESS) in
  let result = Proc.PM.run Proc.proc in
  Lwt.return result

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
       ; let _ = experiment participants in
         Comm.perform ()
