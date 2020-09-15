open Comm

module type PROCESS_FUNCTOR =  functor (MP : PipelineLib.Proc.ProcessMonad) ->
    sig
      module PM :
        sig
          type 'x t = 'x MP.t
          val run : 'a1 t -> 'a1
          val send : role -> role -> 'a1 -> unit t
          val recv : role -> (role -> unit t) -> unit t
          val recv_one : role -> 'a1 t
          val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t
          val pure : 'a1 -> 'a1 t
          val loop : role -> (unit -> 'a1 t) -> 'a1 t
          val set_current : role -> unit t
        end
      val proc : unit MP.t
    end

let execute_process (participants : conn_desc list) mpart : unit =
  Log.log_str "starting" ;
  let mp = Comm.build_participant participants in
  let (module Part : PROCESS_FUNCTOR) = mpart in
  Log.log_str "connections established" ;
  let (module IMP) = mp in
  let (module Proc) = (module Part (IMP) : PROCESS) in
  Log.log_str "running proc" ;
  Proc.proc |> Proc.PM.run
