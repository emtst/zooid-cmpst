open PipelineLib.Code

open Lwt.Infix
open Comm

module type PROCESS =
  sig
    module PM : PipelineLib.Proc.ProcessMonad
    val proc : unit PM.t
end

let experiment (participants : conn_desc list) : unit Lwt.t =
  Log.log_str "starting" ;
  Comm.build_participant participants >>= fun mp ->
  Log.log_str "connections established" ;
  let (module IMP) = mp in
  let (module Proc) = (module ALICE (IMP) : PROCESS) in
  let result = Proc.PM.run Proc.proc in
  Log.log_str "ending" ;
  Lwt.return result

let ralice = 0
let rbob = 1
let rcarol = 2

let participants = [
    { role_from = rbob
    ; role_to = ralice
    ; spec =   Server(build_addr "127.0.0.1" 10001)
  }]


let () = print_endline "Implementation for the role of alice in the pipeline"
       ; if Log.create_log "Alice" then print_endline "Logging." else ()
       ; let _ = experiment participants in ()
