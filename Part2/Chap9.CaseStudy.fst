module Chap9.CaseStudy 

open FStar.List.Tot

let total_order (#a : Type) (f : (a -> a -> bool)) =
  (forall a. f a a)
  /\ (forall a1 a2. (f a1 a2 /\ a1 =!= a2) <==> not (f a2 a1))
  /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)
  /\ (forall a1 a2. f a1 a2 \/ f a2 a1)

let total_order_t (a : Type) = f:(a -> a -> bool){ total_order f }

let rec sorted #a (f : total_order_t a) (l : list a)
  : bool 
  = match l with 
  | [] -> true 
  | [x] -> true
  | x :: y :: xs -> x `f` y && sorted f (y :: xs)

let rec count (#a : eqtype) (x : a) (l : list a)
  : nat 
  = match l with 
    | hd :: tl -> (if hd = x then 1 else 0) + count x tl
    | [] -> 0

let rec append_count 
  (#a : eqtype)
  (l1 l2 : list a)
  : Lemma 
      (ensures 
        forall (x : a). count x (append l1 l2) = count x l1 + count x l2       
      )
  = match l1 with 
    | [] -> ()
    | hd :: tl -> append_count tl l2

let mem (#a: eqtype) (i : a) (l : list a)
  : bool 
  = count i l > 0

let rec partition #a (f: a -> bool) (l : list a)
  : x:(list a & list a) { length (fst x) + length (snd x) = length l }
  = match l with 
    | [] -> [], []
    | hd :: tl ->
        let l1, l2 = partition f tl in 
        if f hd 
        then hd::l1, l2 
        else l1, hd::l2 

let rec sort (#a:eqtype) (f : total_order_t a) (l: list a)
  : Tot (list a) (decreases (length l))
  = match l with 
    | [] -> []
    | pivot :: tl ->
        let hi, lo = partition (f pivot) tl in 
        append (sort f lo) (pivot :: sort f hi)

let rec partition_mem 
    (#a:eqtype)
    (f:(a -> bool))
    (l:list a)
  : Lemma 
      ( let l1, l2 = partition f l in 
        (forall x. mem x l1 ==> f x) /\
        (forall x. mem x l2 ==> not (f x)) /\
        (forall x. mem x l = (mem x l1 || mem x l2))
      )
  = match l with 
    | [] -> ()
    | hd :: tl -> partition_mem f tl

let rec sorted_concat 
    (#a : eqtype)
    (f : total_order_t a)
    (l1 : list a { sorted f l1 })
    (l2 : list a { sorted f l2 })
    (pivot : a)
  : Lemma 
      (requires 
        (forall y. mem y l1 ==> y `f` pivot) /\
        (forall y. mem y l2 ==> pivot `f` y)
      )
      (ensures 
        sorted f (append l1 (pivot :: l2))
      )
  = match l1 with 
    | [] -> 
        (*
          sorted (append [] (pivot :: l2))
            == sorted (pivot :: l2)
          これは sorted l2 と forall y. mem y l2 ==> pivot <= y から直ちに従う。
        *)
        ()
    | [_] ->
        (*
            sorted (append [x] (pivot :: l2))
              == sorted (x :: pivot :: l2)
              == x <= pivot &&            ... pre condition: forall y. mem y l1 ==> ~(pivot <= y) から従う
                    sorted (pivot :: l2)  ... sorted l2 と pre-condition: forall y. mem y l2 ==> pivot <= y から従う 
              == true
        *) 
        ()
    | hd1 :: hd2 :: tl -> 
        (*
          sorted (append (hd1 :: hd2:: tl) (pivot :: l2))
            == sorted (hd1 :: append (hd2 :: tl) (pivot :: l2)) ... append の定義より
            == hd1 <= hd2 &&                                 ... sorted l1より従う
                  sorted (append (hd2 :: tl) (pivot :: l2))     ... IH
            == true.
        *)
        sorted_concat f (hd2 :: tl) l2 pivot

let rec append_mem 
  (#t:eqtype)
  (l1 l2 : list t)
  : Lemma 
      (ensures 
        forall a. mem a (append l1 l2) = (mem a l1 || mem a l2)
      )
  = match l1 with 
    | [] -> ()
    | hd::tl -> append_mem tl l2

let is_permutation_of (#a : eqtype) (l m : list a) =
  forall x. count x l = count x m

let rec partition_mem_permutation 
  (#a : eqtype)
  (f : a -> bool)
  (l : list a)
  : Lemma
    (ensures 
      (
        let l1, l2 = partition f l in 
        (forall x. x `mem` l1 ==> f x) /\
        (forall x. x `mem` l2 ==> not (f x)) /\
        (l `is_permutation_of` (l2 @ l1))
      )
    ) 
    (decreases (length l))
  = match l with 
    | [] -> ()
    | hd :: tl -> 
      (*  
        hd::tl `is_permutation_of` (append l1 l2)
          == forall x. count x (hd::tl) == count x (append l1 l2) ... by the definition of is_permutation_of
          == forall x. count x hd::tl == count x l1 + count x l2       ... append_coint
          == 
      *)
        partition_mem_permutation f tl;
        let tl1, tl2 = partition f tl in    
        append_count tl2 tl1;
        // assert (forall x. count x l = count x tl + (if hd = x then 1 else 0));
        // assert (forall x. count x tl = count x tl1 + count x tl2);
        let l1 = if f hd then hd::tl1 else tl1 in
        let l2 = if f hd then tl2 else hd::tl2 in
        // assert (forall x. count x l1 + count x l2 = count x tl + (if hd = x then 1 else 0));
        // assert (forall x. count x l = count x l1 + count x l2);
        append_count l2 l1
        // assert (forall x. count x l = count x (l1@l2))

let perm_app_lemma 
  (#a : eqtype)
  (hd : a)
  (tl l1 l2 : list a)
  : Lemma 
      (requires (tl `is_permutation_of` (l1 @ l2)))
      (ensures ((hd :: tl) `is_permutation_of` (l1 @ (hd::l2))))
  = append_count l1 l2;
    append_count l1 (hd :: l2);    
    ()

let perm_concat_lemma 
  (#a : eqtype)
  (l l1 l2 l1' l2': list a)
  : Lemma 
      (requires 
        (
          (l1 `is_permutation_of` l1') /\ 
          (l2 `is_permutation_of` l2') /\
          (l `is_permutation_of` (l1 @ l2))
        )
      )
      (ensures 
        (l `is_permutation_of` (l1' @ l2'))
      )
  = append_count l1 l2; append_count l1' l2'

let rec sort_correct 
  (#a : eqtype)
  (f : total_order_t a)
  (l : list a)
  : Lemma 
      (ensures
        ( let m = sort f l in 
          sorted f m /\
          l `is_permutation_of` sort f l 
        )
      )
      (decreases (length l))
  = match l with 
    | [] -> ()
    | hd :: tl ->
        let hi, lo = partition (f hd) tl in 
        sort_correct f hi; 
        sort_correct f lo;
        (*
          m == sort (hd :: tl)
            == sort lo `append` (hd :: sort hi)   ... sortの定義より
          に注意して
        *) 
        partition_mem_permutation (f hd) tl;    
        // を使う。すると
        assert (forall x. x `mem` hi ==> hd `f` x); // ... (1)
        assert (forall x. x `mem` lo ==> x `f` hd); // ... (2)
        assert (tl `is_permutation_of` (lo @ hi));  // ... (3)
        // の3つが言える。
        // is_permutation_of の定義より (permutation は 任意のxの countを保存する)
        assert (forall (x: a). x `mem` hi <==> x `mem` sort f hi);
        assert (forall x. x `mem` lo <==> x `mem` sort f lo);
        // であることに注意すると、(1), (2)からsorted_concatのpre-conditionが満たされるので
        sorted_concat f (sort f lo) (sort f hi) hd;
        //　が使えて
        assert (sorted f (sort f lo @ (hd :: sort f hi)));
        // となり、goalの前半が示せる。
        //次にgoalの後半の証明。
        // (3) に IHを使うことにより
        assert (lo `is_permutation_of` sort f lo);
        assert (hi `is_permutation_of` sort f hi);
        // が言えるので、
        perm_concat_lemma tl lo hi (sort f lo) (sort f hi);
        assert (tl `is_permutation_of` ((sort f lo) @ (sort f hi)));
        // よって
        perm_app_lemma hd tl (sort f lo) (sort f hi);
        // を使うことにより
        assert (l `is_permutation_of` ((sort f lo) @ hd :: (sort f hi)));
        // となり、permutatioｎであることも示せた。
        //証明終。
        ()

let rec sort_intricisc (#a : eqtype) (f : total_order_t a) (l:list a)
  : Tot (m: list a { 
            sorted f m /\
            l `is_permutation_of` m
        }) 
        (decreases (length l))
  = match l with 
    | [] -> []
    | pivot :: tl -> 
        let hi, lo = partition (fun x -> pivot `f` x) tl in 
        partition_mem_permutation (fun x -> pivot `f` x) tl;
        sorted_concat f (sort_intricisc f lo) (sort_intricisc f hi) pivot;
        perm_concat_lemma tl lo hi (sort_intricisc f lo) (sort_intricisc f hi);
        perm_app_lemma pivot tl (sort_intricisc f lo) (sort_intricisc f hi);
        sort_intricisc f lo @ (pivot :: sort_intricisc f hi)