open Syntax

type level = int


and kind =
  | Un
  | Lin
  | KGenericVar : Name.t -> kind
  | KVar : kvar ref -> kind

and kvar =
  | KUnbound of Name.t * level
  | KLink of kind


type t =
  | App : Name.t * t list -> t
  | Arrow : t * kind * t -> t
  | GenericVar : Name.t -> t
  | Var : var ref -> t

and var =
  | Unbound of Name.t * level
  | Link of t

type constr =
  | True
  | Eq of t * t
  | KindLeq of kind * kind
  | And of constr list

(** Predefined types *)

let (@->) x y = Arrow (x,Un,y)
let new_y () =
  let y_name = Name.create ~name:"a" () in
  let n = GenericVar y_name in
  (n @-> n) @-> n

let int_name = Name.create ~name:"int" ()
let int : t = App (int_name, [])

let ref_name = Name.create ~name:"ref" ()
let ref x : t = App (ref_name, [x])
