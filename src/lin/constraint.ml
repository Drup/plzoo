module T = Type

type t =
  | True
  | KindLeq of T.kind * T.kind
  | And of t list

let cand l =
  let f a b = match a,b with
    | True, x | x, True -> x
    | And l, x | x, And l -> And (x :: l)
    | _ -> And [a; b]
  in
  List.fold_left f True l

let rec lower = function
  | True -> T.True
  | And l -> T.And (List.map lower l)
  | KindLeq (k1, k2) -> T.KindLeq (k1, k2)

let (~&) = lower
let (===) a b = T.Eq (a, b)
let (&&&) a b = T.And [a ; b]
