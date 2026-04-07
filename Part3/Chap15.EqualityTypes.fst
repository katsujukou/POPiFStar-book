module Chap15.EqualityTypes

// Definitional Equality

type vec (a:Type) : nat -> Type =
  | Nil : vec a 0
  | Cons : #n:nat -> hd:a -> tl:vec a n -> vec a (n + 1)

// a v:vec a n is also has type vec a m 
// when n and m are definitionally equal.

let conv_vec_0 (#a:Type) (v:vec a ((fun x -> x) 0))
  : vec a 0 
  = v

let conv_vec_1 (#a:Type) (v:vec a ((fun x -> x + 1) 0))
  : vec a 1 
  = v  
  
let rec factorial (n:nat) 
  : nat 
  = let open FStar.Mul in 
    if n = 0 then 1 
    else n * factorial (n - 1)

let conv_vec_6 (#a:Type) (v:vec a (factorial 3))
  : vec a 6 
  = v 

let conv_int (x: (fun b -> if b then int else bool) true)
  : int 
  = x + 1 

// Propositional Equality 

type equals (#a : Type) : a -> a -> Type =
  | Refl : #x:a -> equals x x

let z_equalsz 
  : equals 0 0 
  = Refl 

let fact_3_eq_6 
  : equals (factorial 3) 6 
  = Refl #_ #6

let reflexivity #a (x : a)
  : equals x x 
  = Refl 

let symmetry #a (x y : a) (pf : equals x y)
  : equals y x 
  = Refl 

let transitivity #a (x y z : a) (pf1 : equals x y) (pf2 : equals y z)
  : equals x z 
  = Refl 

// Explicitly 

let uip_refl #a (x y : a) (pf: equals x y)
  : equals pf (Refl #a #x)
  = Refl 

// 任意の「等価性の証明」は Refl に等しい。
let uip_refl_explicit #a (x y : a) (pf : equals #a x y)
  : equals #(equals #a x y) pf (Refl #a #x)
  = Refl #(equals #a x y) #pf 

// 「すべてのequality proof は 等価である」
let uniqueness_of_identity_proof 
  #a                        // 型aを勝手に取る 
  (x y : a)                 // x, yをそれぞれ 型　a を持つ項とする
  (pf0 pf1 : equals #a x y)    // pf0, pf1 という２つの x == y の証明があるとする
  : equals #(equals #a x y) pf0 pf1          // それらは等価である
  = Refl #(equals #a x y) #pf0

val ( == ) #a (x y : a) : squash ( equals x y )

// Recall: squashについて
//
// squash p = _:unit{ p }
//
// t ： p なる項 t は、命題　p　の証明を"構成的に"与える
// e.g.) p = equals x y のとき 
//   p に属する唯一の項　Refl は equals x y の構成的証明になっている
//   squash は、構成的な証明項を導入することなく、equals x yと言う事実のみをcontextに加える
//    squash (equals x y) := _:unit{ equals x y }
//   これに属する値は、 equals x yが
//      - 証明できる場合は()のみ。
//      - 証明できない場合は属する値がない。
//   i.e. どの項によって証明されたかどうかは意識せず、証明できるかどうかだけが関心の対象になる
//             ... Proof-irrelevance の意味
// 詳しくは次章で！

(*
構成的証明
  → proof term を明示的に構成する（中身が重要）

squash
  → proof term の存在だけ保持し、中身を不可視にする
   （証明は依然として必要）

Lemma
  → proof obligation を effect として文脈に流す
  （証明自体は SMT / tactic / 手書きなどで discharge）

  特に後ろ2つの関係を、以下の例で見よ：
*)
open FStar.Squash
let one_plus_one_is_two ()
  : (1 + 1 == 2)
  = return_squash (Prims.Refl #int #2) 

// c.f.
let one_plus_one_is_two_lemma ()
  : Lemma (1 + 1 == 2)
  = ()

// Equality Reflection

let pconv_vec_z 
  (#a:Type) (#n:nat) (_:(n == 0)) (v:vec a n)
  : vec a 0 
  = v

let pconv_ab (#a #b : Type) (_:(a == b)) (v:a)
  : b 
  = v

let pconv_der 
  (#a #b : Type)
  (x y : int)
  (h : ((x > 0 ==> a == int) /\
        (y > 0 ==> b == int) /\
        (x > 0 \/ y > 0)))
  (aa:a)
  (bb:b)
  : int 
  = if x > 0 then aa else bb

let eta 
  (#a : Type) 
  (#b : a -> Type)
  (f : (x:a) -> b x)
  : (x:a) -> b x
  = fun x -> f x

open FStar.Tactics.Effect
let funext_on_eta 
  (#a : Type)
  (#b : a -> Type)
  (f g : ((x : a) -> b x))
  (hyp : ((x : a) -> Lemma (f x == g x)))
  : squash (eta f == eta g)
  = admit()

let funext =
  #a:Type ->
  #b:(a -> Type) ->
  f:(x:a -> b x) ->
  g:(x:a -> b x) ->
  Lemma 
    (requires (forall (x:a). f x == g x))
    (ensures f == g)
  
let f (x:nat) : int = 0
let g (x:nat) : int = if x = 0 then 1 else 0
let pos = x:nat{ x > 0 }
let full_funext_false (ax:funext)
  : False 
  = ax #pos f g;
    assert (f == g);
    assert (f 0 == g 0);
    false_elim()

let eta_equiv = 
  #a:Type ->
  #b:(a -> Type) ->
  f:(x:a -> b x) ->
  Lemma (f == eta f)

let eta_equiv_false (ax:eta_equiv)
  : False 
  = funext_on_eta #pos f g (fun _ -> ());
  ax #pos f;
  ax #pos g;
  assert (f == g);
  assert (f 0 == g 0);
  false_elim()

// exercise]
// Leibniz equality 

// Constructive form:
let leq (#a : Type) (x y : a) 
  = p: (a -> Type) -> ((p x -> p y) & (p y -> p x))
// つまり、任意の p : a -> prop に対して、
// p x -> p ｙ，, p y -> p x　をともに呈することができるとき
// x, y はLeibniz equalとする

// Leibniz equalityが同値関係であること：
let leq_refl 
  (#a : Type) 
  (x:a) 
  : leq #a x x
  = fun (p: ((_: a) -> Type)) ->
    (fun (pf:p x) -> pf), (fun (pf:p x) -> pf)

let leq_symm 
  (#a : Type)
  (x y : a)
  (leq_pf : leq x y)
  : leq y x 
  = fun (p:((_:a) -> Type)) ->
      let (px2py, py2px) = leq_pf p in 
      (py2px, px2py)

let leq_trans 
  (#a : Type)
  (x y z :a)
  (leq1 : leq x y)
  (leq2 : leq y z)
  : leq x z 
  = fun (p: ((_: a) -> Type)) ->
      let (px2py, py2px) = leq1 p in
      let (py2pz, pz2py) = leq2 p in 
      (fun (pf:(p x)) -> py2pz (px2py pf)),
       (fun (pf:(p z)) -> py2px (pz2py pf))

let peq_impl_leq (#a:Type) (x y : a) (pf: equals x y)
  : leq x y 
  // F*では, Propositionally equalな２つの項は
  // Definitionally equalでもある
  // よってF*は暗黙的に px : p x を p yに変換できる
  = fun p -> ((fun px -> px), (fun px -> px)) 

let leq_impl_peq (#a:Type) (x y : a) (pf: leq x y)
  : equals x y 
  // p1 : equals x x -> equals x y を取り出せばよい。
  = let (p1, _) = pf (fun (z:a) -> equals x z) in 
    p1 Refl

