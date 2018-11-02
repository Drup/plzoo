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
  | Constructor of Name.t

and expr =
  | V of value
  | Var of Name.t
  | App of expr * expr list
  | Let of Name.t * expr * expr

type decl = {
  name : Name.t ;
  expr : expr ;
}

module Ty = struct
  type kind =
    | Un
    | Lin
    | KVar of Name.t

  type typ =
    | App of Name.t * typ list
    | Arrow of typ * kind * typ
    | Var of Name.t

  type constraints = (kind * kind) list

  type decl = {
    name : Name.t ;
    params : (Name.t * kind) list ;
    constraints : constraints ;
    constructor : Name.t ;
    typ : typ ;
  }

end

type command =
  | Def of decl
  | Type of Ty.decl

module Rename = struct
  module SMap = Map.Make(String)

  type env = {
    env : Name.t SMap.t ;
    tyenv : Name.t SMap.t ;
  }

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
    | Constant _ | Ref _ | Constructor _ as e -> e

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

  let kind ~kenv = function
    | Ty.KVar {name} -> Ty.KVar (find name kenv)
    | Ty.Un | Ty.Lin as k -> k
  let constrs ~kenv l =
    List.map (fun (k1, k2) -> (kind ~kenv k1, kind ~kenv k2)) l
  let rec type_expr ~kenv ~tyenv ~venv = function
    | Ty.Arrow (ty1, k, ty2) ->
      Ty.Arrow (type_expr ~kenv ~tyenv ~venv ty1,
                kind ~kenv k,
                type_expr ~kenv ~tyenv ~venv ty2)
    | Ty.App ({name}, args) ->
      Ty.App (find name tyenv, List.map (type_expr ~kenv ~tyenv ~venv) args)
    | Ty.Var {name} ->
      Ty.Var (find name venv)


  let add_kind ~kenv = function
    | Ty.KVar {name} ->
      if SMap.mem name kenv then
        kenv, Ty.KVar (find name kenv)
      else
        let n = Name.create ~name () in
        add name n kenv, Ty.KVar n
    | Ty.Un | Ty.Lin as k -> kenv, k
  let add_param (kenv, venv, params) (({name} : Name.t), k) =
    let kenv, k = add_kind ~kenv k in
    let n = Name.create ~name () in
    let venv = add name n venv in
    kenv, venv, (n,k)::params
  let add_params l =
    let kenv, venv, l = List.fold_left add_param (SMap.empty, SMap.empty, []) l in
    kenv, venv, List.rev l
  
  let command { env ; tyenv } = function
    | Def { name = {name} ; expr = e } ->
      let e = expr env e in
      let name = Name.create ~name () in
      Def { name ; expr = e }
    | Type { name = {name}; params; constraints; constructor; typ } ->
      let kenv, venv, params = add_params params in
      let constraints = constrs ~kenv constraints in
      let constructor = Name.create ~name:constructor.name () in
      let typ = type_expr ~kenv ~tyenv ~venv typ in
      let name = Name.create ~name () in
      Type { name ; params ; constructor ; constraints ; typ }

end
