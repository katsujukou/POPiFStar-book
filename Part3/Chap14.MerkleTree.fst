module Chap14.MerkleTree

module L = FStar.List 

// length-indexed strings 
let lstring (n:nat) = s:string{ FStar.String.length s == n }

// Concatenating strings sums their lengths 
let concat #n #m (s0 : lstring n) (s1 : lstring m) 
  : lstring (n + m)
  = FStar.String.concat_length s0 s1;
    s0 ^ s1

assume val hash_size : nat 

let hash_t = lstring hash_size 

assume val hash (m:string) : hash_t 

let resource : Type = string

type mtree : nat -> hash_t -> Type =
  | Leaf:
    res:resource ->
    mtree 0 (hash res)
  | Node:
    #n:nat ->
    #hl:hash_t ->
    #hr:hash_t ->
    left:mtree n hl ->
    right:mtree n hr ->
    mtree (n + 1) (hash (concat hl hr))

type branch : Type = | L | R

let res_id_t : Type = list branch 

let rec get 
  (#h : hash_t)
  (ri : res_id_t) 
  (mt : mtree (FStar.List.length ri) h)
  : Tot resource
    (decreases ri)
  = match ri with 
    | [] -> Leaf?.res mt
    | L::rest -> get rest (Node?.left mt) 
    | R::rest -> get rest (Node?.right mt) 

// The Prover

type resource_with_evidence : nat -> Type =
  | RES:
      (res : resource) ->
      (rid : res_id_t) ->
      (hashes : list hash_t { L.length rid == L.length hashes }) -> 
      resource_with_evidence (L.length rid)


let rec get_with_evidence 
  (#h : _)
  (rid : res_id_t)
  (tree : mtree (L.length rid) h)
  : Tot (resource_with_evidence (L.length rid))
        (decreases rid)
  = match rid with 
    | [] -> RES (Leaf?.res tree) [] []
    | bra::rest -> 
        let Node #_ #hl #hr left right = tree in 
        match bra with 
        | L -> 
          let p = get_with_evidence rest left in 
          RES p.res rid (hr :: p.hashes)
        | R -> 
          let p = get_with_evidence rest right in 
          RES p.res rid (hl :: p.hashes)

// The Verifier

let tail #n (p:resource_with_evidence n { n > 0 })
  : resource_with_evidence (n - 1)
  = let _::id_rest = p.rid in
    let _::hs_rest = p.hashes in 
    RES p.res id_rest hs_rest

let rec compute_root_hash 
  (#n : nat)
  (p : resource_with_evidence n)
  : hash_t
  = let RES d rid hashes = p in 
    match rid with 
    | [] -> hash d
    | bra::rest -> 
        let h' = compute_root_hash (tail p) in
        let hd :: _ = hashes in
        match bra with 
        | L -> hash (concat h' hd)
        | R -> hash (concat hd h')

let verify 
  (#h : hash_t) 
  (#n : nat) 
  (p : resource_with_evidence n) 
  (tree : mtree n h)
  : bool
  = compute_root_hash p = h 

