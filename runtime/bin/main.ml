(* Main file *)

let () =
  let _ = Log.create_log "ZooidRuntime" in
  Log.log_str "Run the zooid runtime" ;
  Comm.perform ()
