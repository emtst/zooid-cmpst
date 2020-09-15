(* Main file *)

let () =
  let _ = Log.create_log "zooid" in
  Log.log_str "Run the zooid runtime" ;
  Comm.perform ()
