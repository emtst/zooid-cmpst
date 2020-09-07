(* open PipelineLib.Code *)

open Lwt.Infix


module type Process = functor (MP : PipelineLib.Proc.ProcessMonad) -> sig
  val proc : unit MP.t
end

let experiment () =
  let participants : Comm.conn_desc list = [] in
   Comm.build_participant participants >>= fun mp ->
   let (module IMP) = mp in
   (* let (module A) = (module Process (IMP)) in *)
   (* let _b : (module (type Process(IMP))) = (module BOB) in
    * let _a = (module BOB (IMP)) in *)
   assert false


let () = print_endline "here we will have the implementation of pipeline"
       ; Comm.perform ()
