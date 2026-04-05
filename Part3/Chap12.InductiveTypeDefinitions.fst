module Chap12.InductiveTypeDefinitions

#push-options "--__no_positivity"
noeq 
type dyn = 
  | Bool : bool -> dyn 
  | Int : int -> dyn 
  | Function : (dyn -> dyn) -> dyn 
#pop-options

let loop' (f : dyn)
  : dyn
  = match f with 
  | Function g -> g f 
  | _ -> f 

let loop : dyn 
  = loop' (Function loop')

#push-options "--__no_positivity"
noeq 
type non_positive =
  | NP : (non_positive -> False) -> non_positive
#pop-options

let almost_false (f:non_positive)
  : False 
  = let NP g = f in g f 

let ff 
  : False 
  = almost_false (NP almost_false)

#push-options "--__no_positivity"
noeq 
type also_non_pos (f : Type -> Type) =
  | ANP : f (also_non_pos f) -> also_non_pos f 
#pop-options

let f_false 
  : Type -> Type 
  = fun a -> (a -> False)

let almost_false_again 
  : f_false (also_non_pos f_false)
  = fun x -> let ANP h = x in h x 

let ff_again 
  : False 
  = almost_false_again (ANP almost_false_again)

noeq 
type free 
    (f:([@@@ strictly_positive] Type -> Type))
    (a:Type)
  : Type =
  | Leaf : a -> free f a 
  | Branch : f (free f a) -> free f a 
