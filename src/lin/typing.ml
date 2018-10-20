open Syntax
module T = Type
module C = Constraint


type scheme = {
  constr : C.t ;
  ty : T.t
}

let fail fmt =
  Zoo.error ~kind:"Type error" fmt

let new_var level = T.Var (ref (T.Unbound(Name.create (), level)))
let new_gen_var () = T.GenericVar(Name.create ())
let ischema ty = { constr = C.True ; ty }


(** Unification *)
module Unif = struct

  exception Fail of T.t * T.t

  let occurs_check_adjust_levels tvar_id tvar_level ty =
    let rec f : T.t -> _ = function
      | T.Var {contents = T.Link ty} -> f ty
      | T.GenericVar _ -> assert false
      | T.Var ({contents = T.Unbound(other_id, other_level)} as other_tvar) ->
        if other_id = tvar_id then
          fail "Recursive types"
        else
          other_tvar := Unbound(other_id, min tvar_level other_level)
      | T.App(ty, ty_arg) ->
        f ty ;
        f ty_arg
      | T.Arrow(param_ty, return_ty) ->
        f param_ty ;
        f return_ty
      | T.Const _ -> ()
    in
    f ty


  let rec unify
    = fun ty1 ty2 -> match ty1, ty2 with
      | _, _ when ty1 == ty2 -> ()

      | T.Const name1, T.Const name2 when Syntax.Name.equal name1 name2 -> ()

      | T.App(ty1, ty_arg1), T.App(ty2, ty_arg2) ->
        unify ty1 ty2 ;
        unify ty_arg1 ty_arg2

      | T.Arrow(param_ty1, return_ty1), T.Arrow(param_ty2, return_ty2) ->
        unify param_ty1 param_ty2 ;
        unify return_ty1 return_ty2

      | T.Var {contents = Link ty1}, ty2 -> unify ty1 ty2
      | ty1, T.Var {contents = Link ty2} -> unify ty1 ty2

      | T.Var {contents = Unbound(id1, _)},
        T.Var {contents = Unbound(id2, _)} when id1 = id2 ->
        (* There is only a single instance of a particular type variable. *)
        assert false

      | T.Var ({contents = Unbound(id, level)} as tvar), ty
      | ty, T.Var ({contents = Unbound(id, level)} as tvar) ->
        occurs_check_adjust_levels id level ty ;
        tvar := Link ty

      | _, _ ->
        raise (Fail (ty1, ty2))

end
  
let normalize l =
  let rec unify_all = function
    | T.Eq (t, t') -> Unif.unify t t' ; C.True
    | T.And l -> C.cand (List.map unify_all l)
    | T.True -> C.True
  in
  unify_all (T.And l)

let normalize_with_ty (constr, ty) = normalize [constr], ty

(** Generalization *)
module Generalize = struct

  let rec gen_ty level = function
    | T.Var {contents = Unbound(id, other_level)} when other_level > level ->
      T.GenericVar id
    | T.App(ty, ty_arg) ->
      App(gen_ty level ty, gen_ty level ty_arg)
    | T.Arrow(param_ty, return_ty) ->
      Arrow(gen_ty level param_ty, gen_ty level return_ty)

    | T.Var {contents = Link ty} -> gen_ty level ty

    | ( T.GenericVar _
      | T.Var {contents = Unbound _}
      | T.Const _
      ) as ty -> ty

  let rec gen_constraint level = function
    | C.True -> C.True, C.True
    | C.And l ->
      let no_vars, vars =
        List.split @@ List.map (gen_constraint level) l
      in
      (C.cand no_vars , C.cand vars)

  (** The real generalization function that is aware of the value restriction. *)
  let go level constr ty exp =
    if Syntax.is_value exp then
      let constr_no_var, constr = gen_constraint level constr in
      let constr_all = C.cand [constr_no_var; constr] in
      let ty = gen_ty level ty in
      constr_all, { constr ; ty }
    else
      constr, { constr = C.True ; ty }

end
let generalize = Generalize.go
  
(** Instance *)
module Instanciate = struct

  let rec instance_ty ~level ~tbl = function
    | T.Const _ as ty -> ty
    | T.Var {contents = Link ty} -> instance_ty ~level ~tbl ty
    | T.GenericVar id ->
      begin try
          Hashtbl.find tbl id
        with Not_found ->
          let var = new_var level in
          Hashtbl.add tbl id var ;
          var
      end
    | T.Var {contents = Unbound _} as ty -> ty
    | T.App(ty, ty_arg) ->
      App(instance_ty ~level ~tbl ty, instance_ty ~level ~tbl ty_arg)
    | T.Arrow(param_ty, return_ty) ->
      Arrow(instance_ty ~level ~tbl param_ty, instance_ty ~level ~tbl return_ty)

  let rec instance_constr ~level ~tbl = function
    | C.True -> T.True
    | C.And l ->
      T.And (List.map (instance_constr ~level ~tbl) l)

  let go level { constr ; ty } =
    let tbl = Hashtbl.create 10 in
    (instance_constr ~level ~tbl constr,
     instance_ty ~level ~tbl ty)

end
let instantiate = Instanciate.go
  
let constant = let open T in function
  | Int _ -> ischema int
  | Plus  -> ischema (int @-> int @-> int)
  | NewRef ->
    let a = new_gen_var () in
    ischema (a @-> T.App (ref, a))
  | Get ->
    let a = new_gen_var () in
    ischema ( T.App (ref, a) @-> a )
  | Set ->
    let a = new_gen_var () in
    ischema ( T.App (ref, a) @-> a @-> a )
      
let rec infer_value env level = function
  | Constant c ->
    normalize_with_ty @@ instantiate level @@ constant c
  | Y ->
    normalize_with_ty @@ instantiate level @@ ischema @@ T.new_y ()
  | Lambda(param, body_expr) ->
    let param_ty = new_var level in 
    let param_scheme = ischema param_ty in
    let fn_env = T.Env.add param param_scheme env in
    let constr, return_ty = infer fn_env level body_expr in
    constr, T.Arrow (param_ty, return_ty)
  | Ref v ->
    let constr, ty = infer_value env level !v in
    constr, T.App (T.ref, ty)

and infer env level : _ -> C.t * T.t = function
  | V v ->
    infer_value env level v

  | Var name ->
    normalize_with_ty @@ instantiate level @@ T.Env.find name env

  | Let(var_name, value_expr, body_expr) ->
    let var_constr, var_ty = infer env (level + 1) value_expr in
    let generalized_constr, generalized_scheme =
      generalize level var_constr var_ty value_expr
    in
    let env = T.Env.add var_name generalized_scheme env in
    let body_constr, body_ty = infer env level body_expr in
    let constr = normalize C.[
        ~&generalized_constr ;
        ~&body_constr ;
      ]
    in
    constr, body_ty
  | App(fn_expr, arg) ->
    let f_constr, f_ty = infer env level fn_expr in
    infer_app env level [C.lower f_constr] f_ty arg

and infer_app env level constr f_ty = function
  | [] -> normalize constr, f_ty
  | e::t ->
    let constr_ty, param_ty = infer env level e in
    let return_ty = new_var level in
    let constr =
      C.lower constr_ty ::
      C.(f_ty === T.(param_ty @-> return_ty)) ::
      constr
    in
    infer_app env level constr return_ty t

let infer_top env e =
  let constr, ty = infer env 1 e in
  let constr1, { constr ; ty } = generalize 0 constr ty e in
  { constr = C.cand [constr; constr1]; ty}
