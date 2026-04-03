module Chap3.PolymorphismAndTypeInference

let apply (a b : Type) (f : a -> b) (x : a) : b = f x 

let compose (a b c : Type) 
  (g : b -> c) 
  (f : a -> b) 
  : a -> c 
  = fun x -> g (f x)

let twice (a : Type) 
  (f : a -> a) 
  (x : a) = 
  compose a a a f f x 

let id (a : Type) (x : a) : a = x 
