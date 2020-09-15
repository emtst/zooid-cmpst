open PipelineLib.Code

open Comm

module type PROCESS =
  sig
    module PM : PipelineLib.Proc.ProcessMonad
    val proc : unit -> unit PM.t
end

let experiment (participants : conn_desc list) : unit =
  Log.log_str "starting" ;
  let mp = Comm.build_participant participants in
  Log.log_str "connections established" ;
  let (module IMP) = mp in
  let (module Proc) = (module ALICE (IMP) : PROCESS) in
  Log.log_str "running proc" ;
  Proc.proc () |> Proc.PM.run




let ralice = 0
let rbob = 1
let rcarol = 2

let participants = [
    { role_from = ralice
    ; role_to = rbob
    ; spec =   Server(build_addr "127.0.0.1" 10001)
  }]


let () = print_endline "Implementation for the role of alice in the pipeline"
       ; if Log.create_log "Alice" then print_endline "Logging." else ()
       ; let _ = experiment participants in ()
