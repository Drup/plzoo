type level = int

and kind =
  | Un
  | Lin
  | KGenericVar : Name.t -> kind
  | KVar : kuvar ref -> kind

and kuvar =
  | KUnbound of Name.t * level
  | KLink of kind

type typ =
  | App : Name.t * typ list -> typ
  | Arrow : typ * kind * typ -> typ
  | GenericVar : Name.t -> typ
  | Var : uvar ref -> typ

and uvar =
  | Unbound of Name.t * level
  | Link of typ

type constr =
  | True
  | Eq of typ * typ
  | KindLeq of kind * kind
  | And of constr list

type normalized_constr = (kind * kind) list

type scheme = {
  kvars : Name.t list ;
  tyvars : (Name.t * kind) list ;
  constr : normalized_constr ;
  ty : typ ;
}

type kscheme = {
  kvars : Name.t list ;
  constr : normalized_constr ;
  args : kind list ;
  kind : kind ;
}


let var ~name level =
  let n = Name.create ~name () in
  n, Var (ref (Unbound(n, level)))
let kind ~name level =
  let n = Name.create ~name () in
  n, KVar (ref (KUnbound(n, level)))
let gen_var () = let n = Name.create () in n, GenericVar n

let tyscheme ?(constr=[]) ?(kvars=[]) ?(tyvars=[]) ty =
  { constr ; kvars ; tyvars ; ty }

let kscheme ?(constr=[]) ?(kvars=[]) ?(args=[]) kind =
  { constr ; kvars ; args ; kind }
