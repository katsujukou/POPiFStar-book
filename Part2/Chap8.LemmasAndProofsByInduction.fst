module Chap8.LemmasAndProofsByInduction 

open FStar.List.Tot
open FStar.List.Tot.Properties
open Chap2.GettingOffTheGround
open Chap7.ProofsOfTermination

let rec factorial_is_greater_than_arg (x : int)
  : Lemma 
      (requires x > 2)
      (ensures factorial' x > x)
  = match x with 
    | 3 -> ()
    | _ -> 
        factorial_is_greater_than_arg (x - 1)

// 0 1 2 3 4 5
// 1 1 2 3 5 8

// 0 1 2 3 4 5 6
// 0 1 1 2 3 5 8
let rec fibonacci_gt_arg (n:nat{ n >= 5})
  : Lemma (fibonacci' n >= n)
  = match n with 
    | 5 -> ()
    | _ ->  
        fibonacci_gt_arg (n - 1)

let rec app #a (l1 l2 : list a)
  : list a 
  = match l1 with 
    | [] -> l2 
    | hd :: tl -> hd :: app tl l2

let rec app_length 
  (#a : Type) 
  (l1 l2 : list a)
  : Lemma 
      (length (app l1 l2) = length l1 + length l2)
  = match l1 with 
    | [] -> ()
    | _ :: tl -> app_length tl l2
        // length (app (hd::tl) l2) 
        //    == length (hd :: (app tl l2)) -- by definition of app
        //    == 1 + length (app tl l2)     -- by definition of length
        //    == 1 + length tl + length l2  -- by induction hypothesis
        //    == length (hd :: tl) + length l2 -- this is RHS.

let snoc #a (l : list a) (h : a) : list a = append l [h]

let rec reverse #a (l:list a)
  : list a 
  = match l with 
  | [] -> []
  | hd :: tl -> reverse tl `snoc` hd

let rec reverse_append #a 
  (xs ys : list a)
  : Lemma 
      (reverse (xs `append` ys) == reverse ys `append` reverse xs)
  = match xs with 
    | [] -> append_l_nil (reverse ys)
    | xh :: xt ->
        (*
          reverse ((hd :: tl) `append` ys)
              == reverse (hd :: (tl `append` ys))
              == reverse (tl `append` ys ) `snoc` hd
              == (reverse ys `append` reverse tl) `append` [hd] -- IH
              == reverse ys `append` (reverse tl `append` [hd]) -- append_assoc
        *)
        reverse_append xt ys;
        append_assoc (reverse ys) (reverse xt) [xh]

    (*
      reverse (xs `snoc` x) == reverse (xs `append` [x])
          == reverse [x] `append` reverse xs 
          == [x] `append` reverse xs
    *)
let rec reverse_is_involutive #a (xs : list a) 
  : Lemma (reverse (reverse xs) == xs)
  = match xs with 
    | [] -> ()
    | hd :: tl -> 
        (*
          reverse (reverse (hd :: tl))        -- by rewriting the inner reverse 
            == reverse (reverse tl `snoc` hd)    with the definition of reverse
            == hd :: reverse (reverse tl)     -- reverse_snoc_lemma
            == hd :: tl                       -- by the induction hypothesis
        *)
        reverse_append (reverse tl) [hd];
        reverse_is_involutive tl

let reverse_is_injective #a (l1 l2 : list a)
  : Lemma 
      (requires reverse l1 == reverse l2)
      (ensures l1 == l2)
  = reverse_is_involutive l1; reverse_is_involutive l2

let rec fold_left #a #b (f: b -> a -> a) (l: list b) (acc:a)
  : a
  = match l with
    | [] -> acc
    | hd :: tl -> fold_left f tl (f hd acc)

let rec fold_left_Cons_aux (#a: Type) (l : list a) (acc : list a)
  : Lemma 
      (fold_left Cons l acc == reverse l `append` acc)
  = match l with
    | [] -> ()
    | hd::tl -> 
        (*
          fold_left Cons (hd :: tl) acc 
            == fold_left Cons tl (hd :: acc)    ... definition of fold_left
            == reverse tl `append` (hd :: acc)  ... IH
            == (reverse tl `append` [hd]) `append` acc ... Fstar.List.Tot.Properties.append_l_cons 
            == (reverse tl `append` reverse [hd]) `append` acc
            == (reverse (hd :: tl)) `append` acc    ... reverse_append
        *)
        fold_left_Cons_aux tl (hd :: acc);
        append_l_cons hd acc (reverse tl)

let fold_left_Cons_is_rev (#a:Type) (l:list a)
  : Lemma (fold_left Cons l [] == reverse l)
  = fold_left_Cons_aux l []; 
    append_l_nil (reverse l)