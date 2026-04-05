module Chap6.InductiveTypesAndPatternMatching

type three = 
  | One_of_three : three 
  | Two_of_three : three 
  | Three_of_three : three

let distinct = assert (
  One_of_three <> Two_of_three /\ 
  One_of_three <> Three_of_three /\
  Two_of_three <> Three_of_three
)

let exhaustive (x:three) = assert (
  x = One_of_three \/
  x = Two_of_three \/ 
  x = Three_of_three
)

let is_one (x:three)
  : bool
  = match x with 
    | One_of_three -> true 
    | _ -> false 


let three_as_int (x:three)
  : int
  = if One_of_three? x then 1 
    else if Two_of_three? x then 2 
    else 3

let only_two_as_int (x:three { ~(Three_of_three? x )})
  : int 
  = match x with 
    | One_of_three -> 1
    | Two_of_three -> 2 

type tup2 (a b : Type) =
  | Tup2 : fst:a -> snd:b -> tup2 a b

let mk_tup3 #a #b #c (x: a) (y: b) (z: c) : a & b & c = (x, y, z)

let same_case #a #b #c #d (x: either a b) (y: either c d)
  : bool 
  = match x, y with
    | Inl _, Inl _ -> true 
    | Inr _, Inr _ -> true
    | _, _ -> false

let sum (x:either bool int) (y:either bool int{ same_case x y })
  : z:either bool int{ Inl? z <==> Inl? x }
  = match x, y with 
    | Inl xl, Inl yl -> Inl (xl || yl)
    | Inr xr, Inr yr -> Inr (xr + yr)
  
let rec length #a (xs : list a) : nat = 
  match xs with 
  | [] -> 0 
  | _::tl -> 1 + length tl

let rec append #a (xs ys : list a) 
  : zs:list a{ length zs = length xs + length ys} 
  = match xs with 
    | [] -> ys 
    | hd::tl -> hd :: append tl ys

