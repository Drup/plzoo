type constant =
  | Int of int
  | Plus
  | NewRef
  | Get
  | Set
  | Y

type value =
  | Constant of constant
  | Lambda of Name.t * expr
  | Ref of value ref

and expr =
  | V of value
  | Var of Name.t
  | App of expr * expr list
  | Let of Name.t * expr * expr
type command =
  | Def of Name.t * expr


module Rename = struct
  module SMap = Map.Make(String)

  type env = Name.t SMap.t
  
  let find x env =
    if SMap.mem x env then
      SMap.find x env
    else
      Zoo.error "Unbound variable %s" x

  let add n k env = SMap.add n k env

  let rec value env = function
    | Lambda ({name}, e) ->
      let new_name = Name.create ~name () in
      let env = add name new_name env in
      let e = expr env e in
      Lambda (new_name, e)
    | Constant _ | Ref _ as e-> e

  and expr env = function
    | V v -> V (value env v)
    | Var { name } -> Var (find name env)
    | App (f, l) -> App (expr env f, List.map (expr env) l)
    | Let ({name}, e1, e2) ->
      let e1 = expr env e1 in
      let new_name = Name.create ~name () in
      let env = add name new_name env in
      let e2 = expr env e2 in
      Let (new_name, e1, e2)

  let command env = function
    | Def ({name},e) -> 
      let e = expr env e in
      let new_name = Name.create ~name () in
      Def (new_name, e)

end
