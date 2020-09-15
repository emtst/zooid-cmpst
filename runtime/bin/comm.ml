(* TCP/IP implementation of the communications module *)

open Unix (* using this TCP/IP sockets for now *)

open Lwt.Infix

type role = int

type lbl = int

type channel = Lwt_unix.file_descr

let max_message_length = 8192

(* connection descriptor *)

type connection_spec = Server of sockaddr | Client of sockaddr

let show_sockaddr = function
  | ADDR_UNIX s -> "Unix: "^ s
  | ADDR_INET (ip, port) -> string_of_inet_addr ip ^ ":" ^ string_of_int port

let show_connection = function
  | Server sa -> "Server " ^ show_sockaddr sa
  | Client sa -> "Client " ^ show_sockaddr sa

type conn_desc = { role_from : role; role_to : role; spec : connection_spec }

let show_conn_desc c =
  "(" ^ string_of_int c.role_from
  ^ "|" ^ string_of_int c.role_to
  ^ "|" ^ show_connection c.spec ^ ")"

let show_conn_descs cs = List.map show_conn_desc cs |> String.concat "**"

let get_my_addresses () =
  let hi = gethostname () |> gethostbyname in
  hi.h_addr_list |> Array.to_list

(* Zooid Monadic Runtime *)
(* module Equality =
 *   struct
 *   type sort = role
 *  end *)

module type MP = sig
  type 'a t

  val run : 'a1 t -> 'a1

  val send : role -> lbl -> 'a1 -> unit t

  val recv : role -> (lbl -> unit t) -> unit t

  val recv_one : role -> 'a1 t

  val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t

  val pure : 'a1 -> 'a1 t

  val loop : int -> (unit -> 'a1 t) -> 'a1 t

  val set_current : int -> unit t
end

(* simple dictionary *)

module Dict = Map.Make(Int)

let or_die = function Some v -> v | None -> failwith "or_die called with None"

(* Comm functions *)

let build_addr ip port = ADDR_INET (inet_addr_of_string ip, port)

(* server accepts a connection *)
let server_accept (sa : sockaddr) =
  Log.log_str "creating socket" ;
  let socket = Unix.socket PF_INET SOCK_STREAM 0 in
  Log.log_str "binding socket" ;
  Unix.bind socket sa ;
  Log.log_str "listening socket" ;
  Unix.listen socket 0;
  Log.log_str "accepting socket" ;
  let (ch, _) = Unix.accept socket in
  Log.log_str "closing socket" ;
  Unix.close socket ; ch

(* client requests a connection *)
let client_request addr =
  let socket = Unix.socket PF_INET SOCK_STREAM 0 in
  Unix.connect socket addr ; socket

(* Function that sets up the connection and implements the monad *)
let setup_channels (conns : conn_desc list) :
    channel Dict.t =
  let conn_desc_to_ch (conn : conn_desc) : (role * Unix.file_descr)=
    let s  = match conn.spec with
    | Server addr ->
       Log.log_str "setting up a server connection" ;
       server_accept addr
    | Client addr -> client_request addr
    in  (conn.role_to, s)
  in
  Log.log_str ("about to start connections: " ^ show_conn_descs conns) ;
  let cs = List.map conn_desc_to_ch conns in
  List.fold_left
    (fun dict (role, ch) -> Dict.add role (Lwt_unix.of_unix_file_descr ch) dict)
    Dict.empty cs

(* test for the channel setup function *)

(* let test_channel_setup () =
 *   print_endline "Testing channel setup (remove from finished code)";
 *   Log.log_str "Testing channel setup" ;
 *   let role_a : role = 0 in
 *   let role_b : role = 1 in
 *   let cs : conn_desc list =
 *     (\* TODO: role as ints, consider moving to strings or variables *\)
 *     [
 *       {
 *         role_from = role_a;
 *         role_to = role_b;
 *         spec = Server (build_addr "127.0.0.1" 13245);
 *       };
 *       {
 *         role_from = role_b;
 *         role_to = role_a;
 *         spec = Client (build_addr "127.0.0.1" 13245);
 *       };
 *     ]
 *   in
 *   let _d = setup_channels cs in
 *   Log.log_str "channels setup successfully" ;
 *   let chs = assert false in (\* collect al the channels in the dict *\)
 *   List.iter (fun _ch -> Lwt_unix.close _ch >>= fun () -> Lwt.return ()) chs
 *   >>= fun () ->
 *   Log.log_str "channels closed" ;
 *   print_endline "Ok.";
 *   Lwt.return () *)

let build_participant (conn : conn_desc list) : (module MP) =
  let current_loop : int option ref = ref None in
  Log.log_str "about to setup channels" ;
  let part_to_ch = setup_channels conn in
  let ch_str = Seq.fold_left
                 (fun xs (x, _) -> string_of_int x ^ ", " ^ xs ) ""  (Dict.to_seq part_to_ch)
  in
  Log.log_str ("channels setup:" ^ ch_str);
  let send' role payload =
    let buff = Marshal.to_bytes payload [] in
    let l = Bytes.length buff in
    Log.log_str ("about to send: " ^ string_of_int role) ;
    Lwt_unix.send (Dict.find role part_to_ch) buff 0 l [] >>= fun l' ->
    assert (l = l');
    Lwt.return l'
  in
  let recv' role =
    let buff = Bytes.create max_message_length in
    Log.log_str "about to recv" ;
    Lwt_unix.recv (Dict.find role part_to_ch) buff 0 max_message_length []
    >>= fun _l -> Marshal.from_bytes buff 0 |> Lwt.return
  in
     (module struct
      type 'a t = 'a Lwt.t

      let run p = Log.log_str "running main" ; Lwt_main.run p

      (* communication primitives *)
      let send role lbl _payload =
        send' role lbl >>= fun _ ->
        send' role _payload >>= fun _ -> Lwt.return ()

      let recv role cont = recv' role >>= fun lbl' -> cont lbl'

      let recv_one = recv'

      (* monadic code *)
      let bind am af = Lwt.( >>= ) am af

      let pure x = Lwt.return x

      let string_of_current () =
        match !current_loop with
        | Some x -> string_of_int x
        | None -> "none"

      (* recursion *)
      let rec loop id proc =
        bind (Log.log_str "about to proc" ; proc ()) (fun x ->
            Log.log_str ("curent_loop: " ^ string_of_current ()) ;
            Log.log_str ("new loop: " ^ string_of_int id) ;
            if !current_loop = Some id then (
              current_loop := None;
              Log.log_str "about to loop again" ;
              loop id proc )
            else pure x)

      let set_current id =
        "set_current: " ^ string_of_int id  |> Log.log_str ;
        current_loop := Some id;
        pure ()
    end : MP)

let perform () =
  let addrs = get_my_addresses () |> List.map string_of_inet_addr in
  "Host: " ^ gethostname () ^ " IPs: " ^ String.concat ", " addrs |> print_endline;
  (* test_channel_setup () |> Lwt_main.run *) ()

(* let toto = Pervasives.succ
 *
 * let run_something conn =
 *   build_participant conn >>= fun mp ->
 *   let (module MP) = mp in
 *   let _bob_mp =
 *     MP.loop 0
 *       (MP.recv 0 (fun l ->
 *            if eqn l (Pervasives.succ 0)
 *            then MP.bind (MP.recv_one 0) (fun x ->
 *                     MP.bind
 *                       (MP.send (Pervasives.succ (Pervasives.succ 0))
 *                          (Pervasives.succ 0)
 *                          (muln x (Pervasives.succ (Pervasives.succ 0)))) (fun _ ->
 *                         MP.set_current (subn (Pervasives.succ 0) 0)))
 *            else MP.pure ()))
 *   in
 *   Lwt.return () *)
