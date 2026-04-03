module Chap2.GettingOffTheGround

(* This is a block comment *)

// This is a line comment 

let even = n:int{ n % 2 = 0 }

let odd = n:int{ n % 2 = 1 }

let f (x: even) :odd = x + 1 

open FStar.Mul

let rec factorial' (n : nat) : nat =
  if n <= 0 then 1 
  else n * factorial' (n - 1)

let rec factorial_helper (acc n : nat) : Tot nat 
  (decreases n) =
    if n <= 0 then acc 
    else factorial_helper (acc * n) (n - 1)

let factorial (n : nat) : nat = factorial_helper 1 n 

let rec factorial_helper_lemma 
  (acc n : nat)
  : Lemma 
      (ensures factorial_helper acc n == acc * factorial' n)
      (decreases n)
  = if n <= 0 then ()
    else factorial_helper_lemma (acc * n) (n - 1)
  
let incr (x : int) : int = x + 1

let max (x:int) (y:int) 
  : z:int{ (x >= y /\ z = x) \/ (x < y /\ z = y) } 
  = if x >= y then x else y
  
let rec fibonacci (n : nat) 
  : nat
  = if n <= 1 then 1 
    else fibonacci (n - 1) + fibonacci (n - 2)
    
  