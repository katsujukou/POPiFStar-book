module Chap4.InterfacingWithAnSMT


let max x y = if x > y then x else y 

let _ = assert (max 0 1 = 1)

let _ = assert 
  (forall x y. 
      max x y >= x /\ 
      max x y >= y /\
      (max x y = x \/ max x y = y))
      