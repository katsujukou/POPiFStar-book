module Chap8.CaseStudy 

open FStar.List.Tot

let rec sorted ( l: list int)
  : bool 
  = match l with 
  | [] -> true 
  | [x] -> true
  | x :: y :: xs -> x <= y && sorted (y :: xs)

let rec mem 
  (#a: eqtype)
  (i : a)
  (l : list a) 
  : bool 
  = match l with 
    | [] -> false 
    | hd :: tl -> i = hd || mem i tl 

let rec partition #a (f: a -> bool) (l : list a)
  : x:(list a & list a) { length (fst x) + length (snd x) = length l }
  = match l with 
    | [] -> [], []
    | hd :: tl ->
        let l1, l2 = partition f tl in 
        if f hd 
        then hd::l1, l2 
        else l1, hd::l2 

let rec sort (l: list int)
  : Tot (list int) (decreases (length l))
  = match l with 
    | [] -> []
    | pivot :: tl ->
        let hi, lo = partition ((<=) pivot) tl in 
        append (sort lo) (pivot :: sort hi)

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
    (l1 : list int { sorted l1 })
    (l2 : list int { sorted l2 })
    (pivot : int)
  : Lemma 
      (requires 
        (forall y. mem y l1 ==> ~(pivot <= y)) /\
        (forall y. mem y l2 ==> pivot <= y)
      )
      (ensures 
        sorted (append l1 (pivot :: l2))
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
        sorted_concat (hd2 :: tl) l2 pivot

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

let rec sort_correct 
  (l:list int)
  : Lemma 
      (ensures
        ( let m = sort l in 
          sorted m /\
          (forall i. mem i l = mem i m)
        )
      )
      (decreases (length l))
  = match l with 
    | [] -> ()
    | hd :: tl ->
        let hi, lo = partition ((<=) hd) tl in 
        sort_correct hi; sort_correct lo;
        (*
          m == sort (hd :: tl)
            == sort lo `append` (hd :: sort hi)   ... sortの定義より
          に注意して
        *) 
        append_mem (sort lo) (hd :: sort hi);
        // を使う。すると
        // 　　forall i. mem i m 
        //      == mem i (sort lo @ (hd :: sort hi))              ... unfold m
        //      == mem i (sort lo) || mem i (hd :: sort hi)       ... append_mem
        //      == mem i (sort lo) || i == hd || mem i (sort hi)  ... unfold mem
        //      == mem i lo || i == hd || mem i hi  ... (1)       ... IH
        // がいえる。
        //つぎに
        partition_mem ((<=) hd) tl;        
        // を使う。すると
        //      (2) forall x. mem x hi ==> hd <= x
        //      (3) forall x. mem x lo ==> not (hd <= x) ie. x > hd
        //      (4) forall x. mem x tl = (mem x hi || mem x lo)
        // の３つが言える。
        //  (4)から, (1)は
        //       mem i lo || mem i hi == mem i tl 
        //   であるので, mem i m == mem i tl || i == hd == mem i l 
        //      
        // 次に、(2), (3)に IH を使うことにより
        //      (2)' forall x. mem x (sort hi) ==> hd <= x 
        //      (3)' forall x. mem x (sort lo) ==> not (hd <= x) 
        // となって sorted_concat の pre-conditionがすべて満たされ
        sorted_concat (sort lo) (sort hi) hd;
        // が使える。これより 
        //   sorted (sort lo `append` (hd :: sort hi))
        //      == sorted m 
        // が従う。
        // 証明終.
        ()

let rec sort_intricisc (l:list int)
  : Tot (m: list int { 
            sorted m /\
            (forall i. mem i l = mem i m)
        }) 
        (decreases (length l))
  = match l with 
    | [] -> []
    | pivot :: tl -> 
        let hi, lo = partition (fun x -> pivot <= x) tl in 
        partition_mem (fun x -> pivot <= x) tl;
        sorted_concat (sort_intricisc lo) (sort_intricisc hi) pivot;
        append_mem (sort_intricisc lo) (pivot :: sort_intricisc hi);
        append (sort_intricisc lo) (pivot :: sort_intricisc hi)