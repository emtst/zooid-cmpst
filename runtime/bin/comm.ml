(* TCP/IP implementation of the communications module *)

open Unix (* using this TCP/IP sockets for now *)


(* connection descriptor *)

type conn_desc =
  { role_from : string
  ; role_to : string
  }


let get_my_addresses () =
  let hi = gethostname () |> gethostbyname in
  hi.h_addr_list |> Array.to_list

(* Zooid Monadic Runtime *)
type __ = Obj.t

module Equality =
  struct
  type sort = __
 end

module type MP =
 sig
  type 'a t

  val send : Equality.sort -> Equality.sort -> 'a1 -> unit t

  val recv : (Equality.sort -> unit t) -> unit t

  val recv_one : Equality.sort -> 'a1 t

  val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t

  val pure : 'a1 -> 'a1 t

  val loop : int -> 'a1 t -> 'a1 t

  val set_current : int -> unit t
 end

let build_participant (_conn : conn_desc list) : (module MP) =
  let current_loop : int option ref = ref None in
  (module struct
     type 'a t = M of 'a

     (* communication primitives *)
     let send = failwith ""
     let recv = failwith ""
     let recv_one = failwith ""

     (* monadic code *)
     let bind am af =
       let M a = am in af a
     let pure x = M x

     (* recursion *)
     let rec loop id proc =
       bind proc (fun x ->
           if !current_loop = Some id
           then loop id proc
           else pure x)

     let set_current id =
       current_loop := Some id ; pure ()
   end)

let perform () =
  let addrs = get_my_addresses () |> List.map string_of_inet_addr in
  "Host: " ^ gethostname () ^ " IPs: " ^ String.concat ", " addrs
  |> print_endline
