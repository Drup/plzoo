open Syntax

type level = int

type t =
  | Const : Name.t -> t
  | App : t * t -> t
  | Arrow : t * t -> t
  | GenericVar : Name.t -> t
  | Var : var ref -> t

and var =
  | Unbound of Name.t * level
  | Link of t

type constr =
  | True
  | Eq of t * t
  | And of constr list

module Env = struct
  module M = NameMap
  exception Var_not_found of Name.t
  type 'a env = 'a M.t
  let add k v env = M.add k v env

  let find k env =
    try M.find k env with
      Not_found -> raise (Var_not_found k)

  let empty = M.empty
end

(** Predefined types *)

let (@->) x y = Arrow (x,y)
let new_y () =
  let y_name = Name.create ~name:"a" () in
  let n = GenericVar y_name in
  (n @-> n) @-> n

let int_name = Name.create ~name:"int" ()
let int = Const int_name

let ref_name = Name.create ~name:"ref" ()
let ref = Const ref_name
