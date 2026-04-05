module Chap7.ProofsOfTermination

open FStar.List.Tot.Base
open FStar.List.Tot.Properties
open FStar.Mul



// let rec loop (x: unit) : False = loop x 

let rec length #a (xs: list a) : Tot nat (decreases xs) =
  match xs with
  | [] -> 0
  | _ :: tl -> 1 + length tl

let rec ackermann (m n: nat) : Tot nat (decreases %[m;n]) =
  if m = 0
  then n + 1
  else if n = 0 then ackermann (m - 1) 1 else ackermann (m - 1) (ackermann m (n - 1))

let rec ackermann_flip (n m: nat) : Tot nat (decreases %[m;n]) =
  if m = 0
  then n + 1
  else if n = 0 then ackermann_flip 1 (m - 1) else ackermann_flip (ackermann_flip (n - 1) m) (m - 1)

type tree =
  | Terminal : tree
  | Internal : node -> tree
and node = {
  left:tree;
  data:int;
  right:tree
}

let rec incr_tree (x: tree) : tree =
  match x with
  | Terminal -> Terminal
  | Internal node -> Internal (incr_node node)
and incr_node (x: node) : node =
  { left = incr_tree x.left; data = x.data + 1; right = incr_tree x.right }

let rec foo (l: list int) : Tot int (decreases %[l;0]) =
  match l with
  | [] -> 0
  | x :: xs -> bar xs
and bar (l: list int) : Tot int (decreases %[l;1]) = foo l

let rec fibonacci' (n: nat) : nat =
    if n <= 0 then 0 
    else if n = 1 then 1 
    else  fibonacci' (n - 1) + fibonacci' (n - 2)
//     n -2 -1  0  1  2  3  4  5  6
// fib n  0  0  0  1  1  2  3  5  8

let rec fib (a b n: nat) : Tot nat (decreases n) =
  match n with
  | 0 -> b
  | _ -> fib b (a + b) (n - 1)

let fibonacci (n: nat) : nat = fib 1 0 n

// [研究] fibonacci' と fibonacci の等価性を示そう。

// fib 6 a b == fib 5 b (a + b)
//           == fib 4 (a + b) (a + 2b)
//           == fib 3 (a + 2b) (2a + 3b)
//           == fib 2 (2a + 3b) (3a + 5b)
//           == fib 1 (3a + 5b) (5a + 8b) 
//           == fib 0 (5a + 8b) (8a + 13b)

// In general,
//    fib n a b == fibonacci' n * a + fibonacci' (n + 1) * b
//
// Note: In the case of n = 0 this formula also holds.
//     LHS = fib 0 a b == b 
//     RHS = fibonacci' 0 * a + fibonacci' 1 * b == 0 * a + 1 * b == b  
let rec fib_acc_lemma (n a b: nat)
    : Lemma
      (ensures 
        fib a b n == 
          a * fibonacci' n + 
          b * fibonacci' (n + 1)
      ) 
    = match n with 
      | 0 -> ()
      | 1 -> ()
      | _ ->
        // LHS == fib n a b 
        //     == fib (n - 1) b (a + b)                                       ... by definition of fib
        //     == fibonacci' (n - 1) * b + fibonacci' n * (a + b)             ... by the induction hypothesis
        //     == a * fibonacci' n + b * (fibonacci' n + fibonacci' (n - 1))
        //     == a * fibonacci' n + b * (fibonacci' (n + 1))                 ... by the definition of fibonacci' 
        fib_acc_lemma (n - 1) b (a + b);
        ()


let both_fibonacci_is_equivalent (n : nat)
  : Lemma (ensures 
      fibonacci' n == fibonacci n
    ) 
  = fib_acc_lemma n 1 0;
    ()

let rec reverse' #a (l: list a)
  : list a 
  = match l with 
    | [] -> [] 
    | hd :: tl -> reverse' tl `append` [hd]

let rec rev_aux #a (l1 l2 : list a)
  : Tot 
      (list a)
      (decreases l2)
  = match l2 with
    | [] -> l1
    | hd :: tl -> rev_aux (hd :: l1) tl 

// let append_cons_lemma #a (xs : list a) (hd : a) (tl : list a)
//   : Lemma 
//       (ensures 
//         xs `append` (hd :: tl) == (xs `append` [hd]) `append` tl
//       )
//   = let open FStar.List.Tot.Properties in 
//     append_assoc xs [hd] tl;
//     ()

let reverse #a (xs : list a) 
  : list a 
  = rev_aux [] xs 
  
#push-options "--print_implicits"
let rec rev_aux_lemma #a (soFar xs : list a)
  : Lemma
      (ensures 
        rev_aux soFar xs == reverse' xs `append` soFar)
      (decreases xs)
  = match xs with 
    | [] -> ()
    | hd :: tl ->
        (*
          rev_aux soFar (hd::tl) 
              == rev_aux (hd :: soFar) tl            ... by definition of rev_aux
              == reverse' tl `append` (hd :: soFar)  ... by IH 
              == (reverse' tl `append` [hd]) `append` soFar
        *)
        rev_aux_lemma (hd :: soFar) tl;
        append_assoc (reverse' tl) [hd] soFar
#pop-options

let nil_is_right_unit_of_append #a (xs : list a)
  : Lemma (ensures xs `append` [] == xs)
  = match xs with 
    | [] -> ()
    | hd :: tl -> append_assoc [hd] tl []

let both_reverse_is_equivalent #a (xs : list a)
  : Lemma 
      (ensures reverse' xs == reverse xs)
  = rev_aux_lemma [] xs;
    nil_is_right_unit_of_append (reverse' xs);
    ()