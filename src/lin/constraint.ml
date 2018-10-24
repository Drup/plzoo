module T = Types

type t = T.solved_constr = 
  | True
  | KindLeq of T.kind * T.kind
  | And of t list

module Solved = struct

  let cand l =
    let f a b = match a,b with
      | True, x | x, True -> x
      | And l, x | x, And l -> And (x :: l)
      | _ -> And [a; b]
    in
    List.fold_left f True l

end
  
let rec lower : T.solved_constr -> T.constr = function
  | True -> T.True
  | And l -> T.And (List.map lower l)
  | KindLeq (k1, k2) -> T.KindLeq (k1, k2)


let (<=) a b : T.constr = T.KindLeq (a, b)
let (===) a b : T.constr = T.Eq (a, b)
let (&&&) a b : T.constr = T.And [a ; b]
let cand l : T.constr = T.And l
