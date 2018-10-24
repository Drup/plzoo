open Types

exception Var_not_found of Name.t
exception Type_not_found of Name.t

type ('a, 'b) env = {
  vars : 'a Name.Map.t ;
  types : 'b Name.Map.t ;
}
type t = (scheme, kscheme) env

let add k v { vars ; types } = { types ; vars = Name.Map.add k v vars }
let add_ty k v { vars ; types } = { vars ; types = Name.Map.add k v types }

let find k env =
  try Name.Map.find k env.vars with
    Not_found -> raise (Var_not_found k)
let find_ty k env =
  try Name.Map.find k env.types with
    Not_found -> raise (Type_not_found k)

let rm k { vars ; types } = { types ; vars = Name.Map.remove k vars }
let rm_ty k { vars ; types } = { vars ; types = Name.Map.remove k types }

let empty = { vars = Name.Map.empty ; types = Name.Map.empty }

