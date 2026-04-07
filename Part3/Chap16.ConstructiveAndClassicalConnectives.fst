module Chap16.ConstructiveAndClassicalConnectives

open FStar.Squash
open FStar.Classical.Sugar  

type empty = 
type trivial = | T

let t_True : prop = squash trivial 
let t_False : prop = squash empty 

let constr_conj #p #q (pf_p : p) (pf_q : q)
  : pair p q 
  = Pair pf_p pf_q 

let conj_intro #p #q (pf_p : squash p) (pf_q : squash q)
  : Lemma (p /\ q)
  = ()

let conj_intro_sugar #p #q (pf_p : squash p) (pf_q : squash q)
  : Lemma (p /\ q)
  = introduce p /\ q 
    with pf_p 
    and pf_q

let constr_disj_1 #p #q (pf_p : p) : sum p q = Left pf_p 
let constr_disj_2 #p #q (pf_q : q) : sum p q = Right pf_q 

let intro_disj_1 #p #q (pf_p : squash p) 
  : Lemma (p \/ q)
  = ()  
let intro_disj_2 #p #q (pf_p : squash q) 
  : Lemma (p \/ q)
  = ()  

let elim_disj_1 #p #q (pf_p_and_q : squash (p /\ q))
  : Lemma (ensures p)
  = () 

let elim_disj_1_sugar #p #q (pf_p_and_q : squash (p /\ q))
  : Lemma (ensures p)
  = eliminate p /\ q
    returns p 
    with pf_p pf_q. pf_p


let intro_disj_1_sugar #p #q (pf_p : squash p) 
  : Lemma (p \/ q)
  = introduce p \/ q 
    with Left pf_p

let intro_disj_2_sugar #p #q (pf_q : squash q) 
  : Lemma (p \/ q)
  = introduce p \/ q 
    with Right pf_q

let neg_intro #p (f:squash p -> squash False)
  : squash (~p)
  = introduce p ==> False 
    with pf_p. f pf_p 

let neg_elim 
  #p 
  #q 
  (f:squash (~p)) 
  (x:unit -> Lemma p)
  : squash (~q)
  = eliminate p ==> False 
    with x ()
