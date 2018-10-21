open Syntax
module T = Type
module C = Constraint


type scheme = {
  kvars : Name.t list ;
  tyvars : (Name.t * T.kind) list ;
  constr : C.t ;
  ty : T.t
}

type kscheme = {
  kvars : Name.t list ;
  constr : C.t ;
  args : T.kind list ;
  kind : T.kind ;
}

let fail fmt =
  Zoo.error ~kind:"Type error" fmt

let new_var ?name level =
  let n = Name.create ?name () in
  n, T.Var (ref (T.Unbound(n, level)))
let new_kind level =
  let n = Name.create ~name:"k" () in n, T.KVar (ref (T.KUnbound(n, level)))
let new_gen_var () = let n = Name.create () in n, T.GenericVar n
let tyscheme ?(constr=C.True) ?(kvars=[]) ?(tyvars=[]) ty =
  { constr ; kvars ; tyvars ; ty }
let kscheme ?(constr=C.True) ?(kvars=[]) ?(args=[]) kind =
  { constr ; kvars ; args ; kind }


module Env = struct
  exception Var_not_found of Name.t
  exception Type_not_found of Name.t

  type ('a, 'b) env = {
    vars : 'a NameMap.t ;
    types : 'b NameMap.t ;
  }
  type t = (scheme, kscheme) env

  let add k v { vars ; types } = { types ; vars = NameMap.add k v vars }
  let add_ty k v { vars ; types } = { vars ; types = NameMap.add k v types }

  let find k env =
    try NameMap.find k env.vars with
      Not_found -> raise (Var_not_found k)
  let find_ty k env =
    try NameMap.find k env.types with
      Not_found -> raise (Type_not_found k)

  let rm k { vars ; types } = { types ; vars = NameMap.remove k vars }
  let rm_ty k { vars ; types } = { vars ; types = NameMap.remove k types }

  let empty = { vars = NameMap.empty ; types = NameMap.empty }
end

(** Instance *)
module Instantiate = struct

  let rec instance_type ~level ~tbl = function
    | T.Const _ as ty -> ty
    | T.Var {contents = Link ty} -> instance_type ~level ~tbl ty
    | T.GenericVar id ->
      begin try
          snd @@ Hashtbl.find tbl id
        with Not_found ->
          let name, var = new_var ~name:id.name level in
          Hashtbl.add tbl id (name, var) ;
          var
      end
    | T.Var {contents = Unbound _} as ty -> ty
    | T.App(ty, args) ->
      let args = List.map (instance_type ~level ~tbl) args in
      App(ty, args)
    | T.Arrow(param_ty, return_ty) ->
      Arrow(instance_type ~level ~tbl param_ty,
            instance_type ~level ~tbl return_ty)

  let rec instance_kind ~level ~ktbl = function
    | T.KVar {contents = KLink k} -> instance_kind ~level ~ktbl k
    | T.KVar {contents = KUnbound _} as k -> k
    | T.KGenericVar id -> 
      begin try
          snd @@ Hashtbl.find ktbl id
        with Not_found ->
          let name, var = new_kind level in
          Hashtbl.add ktbl id (name, var) ;
          var
      end
    | T.Un | T.Lin as k -> k

  
  let rec instance_constr ~level ~ktbl = function
    | C.True -> C.True
    | C.KindLeq (k1, k2) ->
      C.KindLeq (instance_kind ~level ~ktbl k1, instance_kind ~level ~ktbl k2)
    | C.And l ->
      C.And (List.map (instance_constr ~level ~ktbl) l)

  let kind_scheme ~level ~kargs ~ktbl { kvars; constr; args; kind } =
    let constr = instance_constr ~level ~ktbl constr in
    let constr =
      List.fold_left2 (fun l k1 k2 -> C.KindLeq (k1, k2) :: l)
        [constr]
        kargs
        args
    in
    let kind = instance_kind ~level ~ktbl kind in
    assert (List.for_all (Hashtbl.mem ktbl) kvars) ;
    (C.And constr, kind)
    
  let typ_scheme ~level ~env ~tbl ~ktbl { constr ; tyvars; kvars; ty } =
    let c = instance_constr ~level ~ktbl constr in
    let ty = instance_type ~level ~tbl ty in
    let env =
      List.fold_left
        (fun env (t,k) ->
           let ty = fst @@ Hashtbl.find tbl t in
           Env.add_ty ty (kscheme (instance_kind ~level ~ktbl k)) env)
        env
        tyvars
    in
    assert (List.for_all (Hashtbl.mem ktbl) kvars) ;
    assert (List.for_all (fun (k,_) -> Hashtbl.mem tbl k) tyvars) ;
    (env, c, ty)

  let go_kind ?(args=[]) level k = 
    let ktbl = Hashtbl.create 10 in
    kind_scheme ~level ~kargs:args ~ktbl k
  let go level env ty = 
    let tbl = Hashtbl.create 10 in
    let ktbl = Hashtbl.create 10 in
    typ_scheme ~level ~env ~tbl ~ktbl ty

end
let instantiate = Instantiate.go


(** Unification *)
module Kind = struct

  exception Fail of T.kind * T.kind

  let did_unify_kind = ref false

  let adjust_levels tvar_id tvar_level kind =
    let rec f : T.kind -> _ = function
      | T.KVar {contents = T.KLink k} -> f k
      | T.KGenericVar _ -> assert false
      | T.KVar ({contents = T.KUnbound(other_id, other_level)} as other_tvar) ->
        if other_id = tvar_id then
          fail "Recursive types"
        else
          other_tvar := KUnbound(other_id, min tvar_level other_level)
      | T.Un | T.Lin -> ()
    in
    f kind

  let rec leq k1 k2 = match k1, k2 with
    | _, _ when k1 == k2
      -> C.True
    | T.Un, _
    | _, T.Lin
      -> C.True
           
    | T.Lin, T.Un
      -> raise (Fail (k1, k2))

    | T.KVar {contents = KUnbound(id1, _)},
      T.KVar {contents = KUnbound(id2, _)} when id1 = id2 ->
      (* There is only a single instance of a particular type variable. *)
      assert false

    | T.KVar {contents = KLink k1}, k2 -> leq k1 k2
    | k1, T.KVar {contents = KLink k2} -> leq k1 k2
  
    | T.KVar ({contents = KUnbound(id, level)} as tvar), (T.Un as ty)
    | (T.Lin as ty), T.KVar ({contents = KUnbound(id, level)} as tvar) ->
      adjust_levels id level ty ;
      tvar := KLink ty ;
      did_unify_kind := true ;
      C.True

    | _, T.KGenericVar _ | T.KGenericVar _, _ ->
      (* Should always have been instanciated before *)
      assert false
  
    | T.KVar _, T.KVar _ -> C.KindLeq (k1, k2)

  let constr = leq
end

let rec infer_kind ~level ~env = function
  | T.Const n -> Instantiate.go_kind level @@ Env.find_ty n env
  | T.App (f, args) ->
    let constrs, args =
      List.fold_left
        (fun (constrs, args) ty ->
           let constr, k = infer_kind ~level ~env ty in
           (constr :: constrs , k::args))
        ([], []) args
    in
    let constr', kind =
      Instantiate.go_kind level ~args @@ Env.find_ty f env
    in
    C.cand (constr' :: constrs), kind
  | T.Arrow (_, _) -> C.True, T.Un
  | T.GenericVar n -> Instantiate.go_kind level @@ Env.find_ty n env
  | T.Var { contents = T.Unbound (n, _) } ->
    Instantiate.go_kind level @@ Env.find_ty n env
  | T.Var { contents = T.Link ty } ->
    infer_kind ~level ~env ty

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
      | T.App(_ty, ty_arg) ->
        List.iter f ty_arg
      | T.Arrow(param_ty, return_ty) ->
        f param_ty ;
        f return_ty
      | T.Const _ -> ()
    in
    f ty

  let rec unify env ty1 ty2 = match ty1, ty2 with
    | _, _ when ty1 == ty2 -> C.True

    | T.Const name1, T.Const name2 when Syntax.Name.equal name1 name2 -> C.True

    | T.App(ty1, ty_arg1), T.App(ty2, ty_arg2) when ty1 = ty2 ->
      C.And (List.map2 (unify env) ty_arg1 ty_arg2)        

    | T.Arrow(param_ty1, return_ty1), T.Arrow(param_ty2, return_ty2) ->
      C.cand [
        unify env param_ty2 param_ty1;
        unify env return_ty1 return_ty2;
      ]

    | T.Var {contents = Link ty1}, ty2 -> unify env ty1 ty2
    | ty1, T.Var {contents = Link ty2} -> unify env ty1 ty2

    | T.Var {contents = Unbound(id1, _)},
      T.Var {contents = Unbound(id2, _)} when id1 = id2 ->
      (* There is only a single instance of a particular type variable. *)
      assert false

    | (T.Var ({contents = Unbound(id, level)} as tvar) as ty1), (ty as ty2)
    | (ty as ty1), (T.Var ({contents = Unbound(id, level)} as tvar) as ty2) ->
      occurs_check_adjust_levels id level ty ;
      tvar := Link ty ;
      let constr1, k1 = infer_kind ~env ~level ty1 in
      let constr2, k2 = infer_kind ~env ~level ty2 in
      C.cand [constr1; constr2; C.KindLeq (k1, k2)]

    | _, _ ->
      raise (Fail (ty1, ty2))

  let constr env t t' = unify env t t'
  
end


let normalize_constr env l =
  let rec unify_all = function
    | T.Eq (t, t') -> Unif.constr env t t'
    | T.KindLeq (k, k') -> Kind.constr k k'
    | T.And l -> C.cand (List.map unify_all l)
    | T.True -> C.True
  in
  let rec simplify k = match k with
    | C.True -> k
    | C.And l -> C.cand @@ List.map simplify l
    | C.KindLeq (k1, k2) -> Kind.constr k1 k2
  in
  let rec loop l =
    Kind.did_unify_kind := false ;
    let l = simplify l in
    if !Kind.did_unify_kind then
      loop l
    else
      l
  in
  loop @@ unify_all (T.And l)

let normalize (env, constr, ty) = env, normalize_constr env [constr], ty

(** Generalization *)
module Generalize = struct

  module S = Set.Make(Name)

  let rec gen_ty ~level ~tyenv = function
    | T.Var {contents = Unbound(id, other_level)} when other_level > level ->
      tyenv := S.add id !tyenv ;
      T.GenericVar id
    | T.App(ty, ty_args) ->
      App(ty, List.map (gen_ty ~level ~tyenv) ty_args)
    | T.Arrow(param_ty, return_ty) ->
      Arrow(gen_ty ~level ~tyenv param_ty, gen_ty ~level ~tyenv return_ty)
    | T.Var {contents = Link ty} -> gen_ty ~level ~tyenv ty
    | ( T.GenericVar _
      | T.Var {contents = Unbound _}
      | T.Const _
      ) as ty -> ty

  let rec gen_kind ~level ~kenv = function
    | T.KVar {contents = KUnbound(id, other_level)} when other_level > level ->
      kenv := S.add id !kenv ;
      T.KGenericVar id
    | T.KVar {contents = KLink ty} -> gen_kind ~level ~kenv ty
    | ( T.KGenericVar _
      | T.KVar {contents = KUnbound _}
      | T.Un | T.Lin
      ) as ty -> ty
  
  let rec gen_constraint ~level ~kenv = function
    | C.True -> C.True, C.True
    | C.KindLeq (k1, k2) ->
      (* let prev_kvars = !kenv in *)
      let k1 = gen_kind ~level ~kenv k1 in
      let k2 = gen_kind ~level ~kenv k2 in
      let constr = C.KindLeq (k1, k2) in
      (* if prev_kvars == !kenv
       * then C.True, constr
       * else constr, C.True *)
      C.True, constr
    | C.And l ->
      let no_vars, vars =
        List.split @@ List.map (gen_constraint ~level ~kenv) l
      in
      (C.cand no_vars , C.cand vars)

  (** The real generalization function that is aware of the value restriction. *)
  let go env level constr ty exp =
    if Syntax.is_value exp then
      let tyenv = ref S.empty in
      let kenv = ref S.empty in
      let constr_no_var, constr = gen_constraint ~level ~kenv constr in
      let constr_all = C.cand [constr_no_var; constr] in
      let ty = gen_ty ~level ~tyenv ty in

      let get_kind (env : Env.t) t =
        match Env.find_ty t env with
        | { kvars = []; constr = C.True; args = [] ; kind } ->
          gen_kind ~level ~kenv kind
        | _ ->
          fail "Higher kinded types are not supported."
      in 
      let tyvars = S.fold (fun ty l -> (ty, get_kind env ty)::l) !tyenv [] in
      let kvars = S.elements !kenv in
      let env = S.fold (fun ty env -> Env.rm_ty ty env) !tyenv env in
      
      env, constr_all, { constr ; tyvars ; kvars ; ty }
    else
      env, constr, { constr = C.True ; kvars = [] ; tyvars = [] ; ty }

end
let generalize = Generalize.go
  
  
let constant = let open T in function
  | Int _ -> tyscheme int
  | Plus  -> tyscheme (int @-> int @-> int)
  | NewRef ->
    let name, a = new_gen_var () in
    tyscheme ~tyvars:[name, Un] (a @-> T.App (ref_name, [a]))
  | Get ->
    let name, a = new_gen_var () in
    tyscheme ~tyvars:[name, Un] ( T.App (ref_name, [a]) @-> a )
  | Set ->
    let name, a = new_gen_var () in
    tyscheme ~tyvars:[name, Un] ( T.App (ref_name, [a]) @-> a @-> a )


let with_binding env x ty f =
  let env = Env.add x ty env in
  let env, constr, ty = f env in
  let env = Env.rm x env in
  env, constr, ty

let with_type ?name ~env ~level f =
  let name, ty = new_var ?name level in
  let kind = kscheme (snd @@ new_kind level) in
  let env = Env.add_ty name kind env in 
  f env ty 

let rec infer_value (env : Env.t) level = function
  | Constant c ->
    instantiate level env @@ constant c
  | Y ->
    let y_name = Name.create ~name:"a" () in
    let n = T.GenericVar y_name in
    let ty = tyscheme ~tyvars:[y_name, Un] T.((n @-> n) @-> n) in
    instantiate level env ty
  | Lambda(param, body_expr) ->
    with_type ~name:param.name ~env ~level @@ fun env param_ty ->
    let param_scheme = tyscheme param_ty in
    with_binding env param param_scheme @@ fun env ->
    let env, constr, return_ty = infer env level body_expr in
    env, constr, T.Arrow (param_ty, return_ty)
  | Ref v ->
    let env, constr, ty = infer_value env level !v in
    env, constr, T.App (T.ref_name, [ty])

and infer (env : Env.t) level : _ -> _ * C.t * T.t = function
  | V v ->
    infer_value env level v

  | Var name ->
    instantiate level env @@ Env.find name env

  | Let(var_name, value_expr, body_expr) ->
    let env, var_constr, var_ty = infer env (level + 1) value_expr in
    let env, generalized_constr, generalized_scheme =
      generalize env level var_constr var_ty value_expr
    in
    let env, body_constr, body_ty = with_binding env var_name generalized_scheme @@
      fun env -> infer env level body_expr
    in
    let constr = normalize_constr env C.[
        ~&generalized_constr ;
        ~&body_constr ;
      ]
    in
    env, constr, body_ty
  | App(fn_expr, arg) ->
    let env, f_constr, f_ty = infer env level fn_expr in
    infer_app env level [C.lower f_constr] f_ty arg

and infer_app (env : Env.t) level constr f_ty = function
  | [] -> env, normalize_constr env constr, f_ty
  | e::t ->
    let env, constr_ty, param_ty = infer env level e in
    with_type ?name:None ~level ~env @@ fun env return_ty ->
    let constr =
      C.lower constr_ty ::
      C.(f_ty === T.(param_ty @-> return_ty)) ::
      constr
    in
    infer_app env level constr return_ty t

let initial_env =
  Env.empty
  |> Env.add_ty T.ref_name (kscheme ~args:[Un] Un)
  |> Env.add_ty T.int_name (kscheme Un)

let infer_top env e =
  let env, constr, ty = infer env 1 e in
  let env, constr, scheme = generalize env 0 constr ty e in
  assert (constr = C.True) ;
  env, scheme
