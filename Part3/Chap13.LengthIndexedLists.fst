module Chap13.LengthIndexedLists 

open FStar.Classical.Sugar
open FStar.Pervasives.Native

type even (a:Type) =
  | ENil : even a 
  | ECons : a -> odd a -> even a 
and odd (a:Type) =
  | OCons : a -> even a -> odd a 

let rec elength #a (e:even a)
  : n:nat { n % 2 == 0 }
  = match e with 
    | ENil -> 0 
    | ECons _ tl -> 1 + olength tl 
and olength #a (o:odd a)
  : n:nat { n % 2 == 1 }
  = let OCons _ tl = o in 
    1 + elength tl 
  
type even_or_odd_list (a : Type) : bool -> Type =
  | EONil : even_or_odd_list a true 
  | EOCons : a -> #b:bool -> even_or_odd_list a b -> even_or_odd_list a (not b)

let rec eo_length #a #b (l:even_or_odd_list a b)
  : Tot (n:nat { if b then n % 2 == 0 else n % 2 == 1})
        (decreases l)
  = match l with 
    | EONil -> 0 
    | EOCons _ tl -> 1 + eo_length tl 

type vec (a : Type) : nat -> Type =
  | Nil : vec a 0
  | Cons : #n:nat -> hd:a -> tl:vec a n -> vec a (n + 1)

let rec get #a #n (i:nat { i < n }) (v:vec a n)
  : a 
  = match v with 
    | Cons hd tl -> 
        if i = 0 then hd 
        else get (i - 1) tl 

let rec append' 
  (#a : Type) 
  (#n #m : nat)
  (v1 : vec a n)
  (v2 : vec a m)
  : GTot (vec a (n + m))
  = match v1 with 
    | Nil -> v2 
    | Cons hd tl -> Cons hd (append' tl v2)

let rec append_v_Nil 
  (#a : Type)
  (#n : nat)
  (v : vec a n)
  : Lemma 
      (ensures 
        v `append'` Nil == v
      )
  = match v with 
    | Nil -> ()
    | Cons _ tl -> append_v_Nil tl 

let append_Nil_v 
  (#a : Type)
  (#n : nat)
  (v : vec a n)
  : Lemma 
      (ensures 
        Nil `append'` v == v
      )
  = match v with 
    | Nil -> ()
    | Cons _ tl -> ()

let rec append_assoc 
  (#a: Type)
  (#n #m #k : nat)
  (v1 : vec a n)
  (v2 : vec a m)
  (v3 : vec a k)
  : Lemma 
    (ensures (v1 `append'` (v2 `append'` v3) == (v1 `append'` v2) `append'` v3)
    )
  = match v1 with 
    | Nil -> ()
    | Cons hd tl -> append_assoc tl v2 v3
  
let rec reverse' 
  (#a : Type)
  (#n : nat)
  (v : vec a n)
  : GTot (vec a n) 
  = match v with 
    | Nil -> Nil
    | Cons hd tl -> append' (reverse' tl) (hd `Cons` Nil)


let rec rev_aux 
  (#a : Type)
  (#n #m : nat)
  (soFar : vec a n)
  (v : vec a m)
  : Tot (vec a (n + m)) (decreases v)
  = match v with 
    | Nil -> soFar
    | Cons hd tl -> rev_aux (hd `Cons` soFar) tl

let reverse (#a : Type) (#n : nat) (v : vec a n) 
  : Tot (vec a n) 
  = rev_aux Nil v

let rec append_cons_lemma 
  (#a : Type)
  (#n #m : nat)
  (v : vec a n)
  (hd : a)
  (tl : vec a m)
  : Lemma 
    (ensures 
      v `append'` (hd `Cons` tl)
        == (v `append'` (hd `Cons` Nil)) `append'` tl
    )
  = match v with 
    | Nil -> ()
    | Cons hd' tl' -> append_cons_lemma tl' hd tl

let rec reverse_append_lemma 
  (#a : Type)
  (#n #m : nat)
  (v1 : vec a n)
  (v2 : vec a m)
  : Lemma 
      (ensures 
        reverse' (v1 `append'` v2)
          == reverse' v2 `append'` reverse' v1
      )
      (decreases n)
  = match v1 with 
    | Nil -> 
        append_Nil_v v2; 
        append_v_Nil (reverse' v2)
    | Cons hd tl -> 
        reverse_append_lemma tl v2;
        append_assoc (reverse' v2) (reverse' tl) (Cons hd Nil);
        ()

#push-options "--split_queries always"
let rec reverse_correct_aux 
  (#a : Type)
  (#n : nat)
  (v : vec a n)
  : Lemma 
      (ensures
        forall (#m : nat) (acc : vec a m).
          rev_aux acc v == reverse' v `append'` acc 
      )
  = match v with 
    | Nil -> ()
    | Cons hd tl ->
        introduce 
          forall (m : nat) (acc : vec a m).
            rev_aux acc v == reverse' v `append'` acc 
        with (
          reverse_correct_aux tl;
          append_cons_lemma (reverse' tl) hd acc;
          reverse_append_lemma (hd `Cons` Nil) tl;
          ()
        )
#pop-options 

let reverse_correct 
  (#a : Type) 
  (#n : nat) 
  (v : vec a n)
  : Lemma 
      (ensures 
        reverse v == reverse' v 
      )
  = reverse_correct_aux v;
    append_v_Nil (reverse' v);
    ()

let rec reverse_is_involutive
  (#a : Type)
  (#n : nat)
  (v : vec a n)
  : Lemma 
      (ensures 
        reverse' (reverse' v) == v
      )
=
  match v with
  | Nil ->
      ()
  | Cons hd tl ->
      reverse_is_involutive tl;
      reverse_append_lemma (reverse' tl) (Cons hd Nil);
      ()

let reverse_singleton
  (#a : Type)
  (hd : a)
  : Lemma 
    (ensures 
      reverse' (hd `Cons` Nil) == hd `Cons` Nil
    )
  = ()

let append
  (#a : Type)
  (#n #m : nat)
  (v1 : vec a n)
  (v2 : vec a m)
  : Tot (vec a (n + m))
  = rev_aux v2 (reverse v1)

let append_correct 
  (#a : Type)
  (#n #m : nat)
  (v1 : vec a n)
  (v2 : vec a m)
  : Lemma 
      (v1 `append` v2 == v1 `append'` v2)
  = match v1 with 
    | Nil -> ()
    | Cons hd tl ->
        reverse_correct v1;
        reverse_correct_aux (append' (reverse' tl) (Cons hd Nil));
        reverse_append_lemma (reverse' tl) (Cons hd Nil);
        reverse_is_involutive tl; 
        ()

let rec take'
  (#a : Type) 
  (#n : nat) 
  (m : nat { m <= n}) 
  (v : vec a n)
  : GTot (vec a m)
  = match m with 
    | 0 -> Nil
    |_ -> let Cons hd tl = v in 
          Cons hd (take' (m - 1) tl)

let rec take_aux
  (#a : Type)
  (#n #k : nat)
  (m : nat { m <= n })
  (v : vec a n)
  (soFar : vec a k)
  : vec a (k + m)
  = if m = 0 then reverse soFar 
    else 
      let Cons hd tl = v in 
      take_aux (m - 1) tl (Cons hd soFar) 

let take
  (#a : Type) 
  (#n : nat) 
  (m : nat { m <= n}) 
  (v : vec a n)
  : vec a m
  = take_aux m v Nil

let rec take_correct_aux
  (#a : Type)
  (#n #k : nat)
  (m : nat { m <= n})
  (v : vec a n)
  (soFar : vec a k)
  : Lemma 
    (ensures 
      take_aux m v soFar == reverse' soFar `append'` take' m v
    )
    (decreases m)
  = match m with 
    | 0 ->
      reverse_correct soFar;
      append_v_Nil (reverse' soFar);
      ()
    | _ -> 
      let Cons hd tl = v in 
      assert (take_aux m v soFar 
        == take_aux (m-1) tl (hd `Cons` soFar)
      );
      take_correct_aux (m-1) tl (hd `Cons` soFar);
      assert (take_aux m v soFar
        == reverse' (hd `Cons` soFar) `append'` take' (m-1) tl 
      );
      assert (reverse' (hd `Cons` soFar) == reverse' soFar `append'` (Cons hd Nil));
      append_assoc (reverse' soFar) (Cons hd Nil) (take' (m-1) tl);
      assert (reverse' (hd `Cons` soFar) `append'` take' (m-1) tl
        == reverse' soFar `append'` ((Cons hd Nil) `append'` take' (m - 1) tl)
      );
      assert (reverse' (hd `Cons` soFar) `append'` take' (m-1) tl
        == reverse' soFar `append'` (take' m (hd`Cons`tl))
      );
      () 

let take_correct 
  (#a : Type)
  (#n : nat)
  (v : vec a n)
  (m : nat { m <= n })
  : Lemma 
    (ensures take m v == take' m v)
  = take_correct_aux m v Nil;
    append_Nil_v (take' m v);
    ()

// これは既に末尾再帰
let rec drop 
  (#a : Type)
  (#n : nat)
  (m : nat { m <= n })
  (v : vec a n)
  : vec a (n - m)
  = match m with 
    | 0 -> v 
    | _ -> let Cons hd tl = v in 
           drop (m - 1) tl

let split_at 
  (#a : Type)
  (#n : nat)
  (i : nat { i <= n })
  (v : vec a n)
  : (vec a i & vec a (n - i))
  = take i v, drop i v

let rec split_at_correct
  (#a:Type)
  (#n:nat)
  (i:nat { i <= n })
  (v:vec a n)
  : Lemma
    (ensures
      (let (l, r) = split_at i v in
      v == l `append'` r)
    )
= match i with 
  | 0 -> ()
  | _ -> 
    let Cons hd tl = v in 
    let (l, r) = split_at i v in
    take_correct v i;
    split_at_correct (i - 1) tl;
    take_correct tl (i - 1)

let rec split_at_intrinsic
  (#a : Type)
  (#n : nat)
  (i : nat { i <= n })
  (v : vec a n)
  : vv:(vec a i & vec a (n - i)) { vv._1 `append'` vv._2 == v }
  = match i with 
    | 0 -> Nil, v 
    | _ -> 
      let Cons hd tl = v in
      let tll, tlr = split_at_intrinsic (i - 1) tl in 
      (Cons hd tll, tlr)