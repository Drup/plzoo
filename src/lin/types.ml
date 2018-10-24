type level = int

and kind =
  | Un
  | Lin
  | KGenericVar : Name.t -> kind
  | KVar : kvar ref -> kind

and kvar =
  | KUnbound of Name.t * level
  | KLink of kind

type typ =
  | App : Name.t * typ list -> typ
  | Arrow : typ * kind * typ -> typ
  | GenericVar : Name.t -> typ
  | Var : var ref -> typ

and var =
  | Unbound of Name.t * level
  | Link of typ

type constr =
  | True
  | Eq of typ * typ
  | KindLeq of kind * kind
  | And of constr list

type solved_constr = 
  | True
  | KindLeq of kind * kind
  | And of solved_constr list

type scheme = {
  kvars : Name.t list ;
  tyvars : (Name.t * kind) list ;
  constr : solved_constr ;
  ty : typ ;
}

type kscheme = {
  kvars : Name.t list ;
  constr : solved_constr ;
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

let tyscheme ?(constr=(True : solved_constr)) ?(kvars=[]) ?(tyvars=[]) ty =
  { constr ; kvars ; tyvars ; ty }

let kscheme ?(constr=(True : solved_constr)) ?(kvars=[]) ?(args=[]) kind =
  { constr ; kvars ; args ; kind }
