(* Lambda-calculus to SKI conversion *)

(* 
#use "skconv.ml";;
*)

(* ------------------------------------------------------------------------ 
 *                      Basic Definitions
 *)

(* Simply-typed lambda-calculus, with De Bruijn indices *)
module type Lam = sig
  type ('g,'a) repr
  val z:   ('a*'g,'a) repr
                                       (* Only open values can be weakened *)
  val s:   ('b*'g,'a) repr -> (_*('b*'g),'a) repr  
  val lam: ('a*'g,'b) repr -> ('g,'a->'b) repr
  val ($$): ('g,'a->'b) repr -> ('g,'a) repr -> ('g,'b) repr (* application *)
end

(* Sample terms *)
module Ex1(L:Lam) = struct
  open L
    (* Unit is for the sake of value restriction *)
  let l1 () = lam z
  let l2 () = lam (lam z)
  let l3 () = lam (lam (s z))
  let l4 () = lam (lam ((s z) $$ z))
  let l5 () = lam (lam (z $$ (s z)))
  let l6 () = lam (lam (lam (z $$ (s (s z)))))
  let l7 () = lam (lam (lam ((lam z) $$ (s (s z)))))
  let l8 () = lam (lam (lam (((s (s z)) $$ z) $$ ((s z) $$ z))))

  (* Bad programs illustrating code explosion *)
  let bad2 () = lam (lam (z $$ s z))
  let bad3 () = lam (lam (lam (z $$ s z $$ s (s z))))
  let bad4 () = lam (lam (lam (lam (z $$ s z $$ s (s z) $$ s (s (s z))))))

  (* Noshita's bad terms  *)
  let nbad4 () = lam (lam (lam
    (lam ((z $$ (s (s z))) $$ (s z $$ s (s (s z)))))))

  let nbad8 () = 
    let x0 = z in
    let x1 = s z in
    let x2 = s (s z) in
    let x3 = s (s (s z)) in
    let x4 = s (s (s (s z))) in
    let x5 = s (s (s (s (s z)))) in
    let x6 = s (s (s (s (s (s z))))) in
    let x7 = s (s (s (s (s (s (s z)))))) in
    lam (lam (lam (lam (lam (lam (lam (lam
      (((x0 $$ x4) $$ (x2 $$ x6)) $$ ((x1 $$ x5) $$ (x3 $$ x7))))))))))
end

(* Computing the size of a term *)
module SizeLam = struct
  type ('g,'a) repr = int
  let z:   ('a*'g,'a) repr = 1
  let s:   ('b*'g,'a) repr -> (_*('b*'g),'a) repr = succ
  let lam: ('a*'g,'b) repr -> ('g,'a->'b) repr = succ
  let ($$): ('g,'a->'b) repr -> ('g,'a) repr -> ('g,'b) repr = 
    fun x y -> x + y + 1
end
  

(* The combinator calculus *)
module type SKI = sig
  type 'a repr
  val kI:  ('a->'a) repr
  val kK:  ('a->'b->'a) repr
  val kS:  (('a->'b->'c)->('a->'b)->'a->'c) repr
  val kB:  (('a -> 'b) -> ('c -> 'a) -> 'c -> 'b) repr
  val kC:  (('a -> 'b -> 'c) -> ('b -> 'a -> 'c)) repr
  val ($!): ('a->'b) repr -> 'a repr -> 'b repr (* application *)
end
;;

let parens t s = if t then "(" ^ s ^ ")" else s

(* One implementation of SKI, to print out terms *)
module PSKI = struct
  type 'a repr = string
  let kI:  ('a->'a) repr = "I"
  let kK:  ('a->'b->'a) repr = "K"
  let kS:  (('a->'b->'c)->('a->'b)->'a->'c) repr = "S"
  let kB:  (('a -> 'b) -> ('c -> 'a) -> 'c -> 'b) repr
          = "B"
  let kC:  (('a -> 'b -> 'c) -> ('b -> 'a -> 'c)) repr
          = "C"
  let ($!): ('a->'b) repr -> 'a repr -> 'b repr = 
    fun f x -> f ^ parens (String.length x > 1) x
end
;;

(* The evaluator, another SKI implementation
   It is just expresses each combinator as an lambda (OCaml) term,
   along with the fact that combinator application is just an OCaml application
   The simple-typed SKI calculus is strongly normalizing. Therefore,
   we pick the most natural, for OCaml embedding, applicative strategy.
   For head-first strategy, see RBigSKI below.
*)

module RSKI = struct
  type 'a repr = 'a
  let kI:  ('a->'a) repr = fun x -> x
  let kK:  ('a->'b->'a) repr = fun x y -> x
  let kS:  (('a->'b->'c)->('a->'b)->'a->'c) repr = 
    fun f g x -> f x (g x)
  let kB:  (('a -> 'b) -> ('c -> 'a) -> 'c -> 'b) repr
          = fun f g x -> f (g x)
  let kC:  (('a -> 'b -> 'c) -> ('b -> 'a -> 'c)) repr
          = fun f g x -> f x g
  let ($!): ('a->'b) repr -> 'a repr -> 'b repr = fun f x -> f x
end
;;

(* Running example of the paper *)
module ExCl5(S:SKI) = struct
  open S
  let l51 = kB $! (kS $! kI) $! (kB $! kK $! (kB $! kI $! kI))
  let l52 = kB $! (kS $! kI) $! (kB $! kK $! kI)
  let l53 = kS $! (kS $! (kK $! kS) $! (kK $! kI)) $!
                  (kS $! (kK $! kK) $! kI)
end
;;

(* Sample evaluation example: reduce a term and show the result
   We use the example suggested by a reviewer, proving that 
   S'IKK(KI) reduces to KI, where S', defined by the rule
   S' t a b x = t (a x) (b x)
  is
  let kS' : 
      (('a -> 'b -> 'c) -> ('d -> 'a) -> ('d -> 'b) -> 'd -> 'c) repr =
   kB $! (kB $! kS) $! kB
*)

let (5,6,7) =
  let open RSKI in
  let kS' : 
      (('a -> 'b -> 'c) -> ('d -> 'a) -> ('d -> 'b) -> 'd -> 'c) =
   kB $! (kB $! kS) $! kB in
  let t = kS' $! kI $! kK $! kK $! (kK $! kI) in
  (t 10 5, t 10 6, t 10 7);;


(* ------------------------------------------------------------------------ 
 * First version of the conversion, typed, but not linear time due to GADT
 * traversals
 *)

(* This is the first, simpler but less optimal version *)
module Conv0(S:SKI) (* : Lam *) = struct
  (* Generally open code with variables x  y ... z where
     z has the highest index and x has the index 0
     is represented as
     D z y ... x where D is closed
     If a term does not have a variable with index 0 as
     free, we add it, using combinators

    Variables are eliminated by eta-reduction
   *)
  type ('g,'a) repr =
    | C: 'a S.repr -> ('g,'a) repr   (* closed code *)
    | N: ('g,'a->'b) repr -> ('a*'g,'b) repr  (* N e === (s e) z *)

  let rec ($$): type g a b. (g,a->b) repr -> (g,a) repr -> (g,b) repr = 
   fun d' d -> match (d',d) with
    | (C d',C d) -> C S.(d' $! d)
    | (C d',N d) -> N (C S.(kB $! d') $$ d)        (* D1 (D2 x) *)
    | (N d',C d) -> N (C S.(kC $! kC $! d) $$ d')  (* (D1 x) D2 *)
    | (N d',N d) -> N ((C S.kS) $$ d' $$ d)        (* (d' x) (d x) *)

  let z:   ('a*'g,'a) repr = N (C S.kI)
  let s:   ('b*'g,'a) repr -> (_*('b*'g),'a) repr = fun e ->
    N ((C S.kK) $$ e)

  let lam: ('a*'g,'b) repr -> ('g,'a->'b) repr = function
    | C k -> C (S.(kK $! k))
    | N x -> x                          (* eta-contraction *)

  let observe : (unit,'a) repr -> 'a S.repr = function
  C x -> x
end

let _ = let module C = Conv0(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l1 ()
;;
(* - : ('_a -> '_a) PSKI.repr = "I" *)

let _ = let module C = Conv0(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l2 ()
;;
(*  - : ('_a -> '_b -> '_b) PSKI.repr = "KI" *)

let _ = let module C = Conv0(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l3 ()
;;
(* - : ('_a -> '_b -> '_a) PSKI.repr = "BKI" *)

let 1 = let module C = Conv0(RSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l3 ()) 1 2
;;

let _ = let module C = Conv0(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l4 ()
;;

(* - : (('_a -> '_b) -> '_a -> '_b) PSKI.repr = "CCI(BS(BKI))" *)

let 5 = let module C = Conv0(RSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l4 ()) succ 4
;;

let _ = let module C = Conv0(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l5 ()
;;

(* - : ('_a -> ('_a -> '_b) -> '_b) PSKI.repr = "B(SI)(BKI)" *)

let 5 = let module C = Conv0(RSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l5 ()) 4 succ
;;


let _ = let module C = Conv0(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l6 ()
;;

(* - : ('_a -> '_b -> ('_a -> '_c) -> '_c) PSKI.repr = "B(B(SI))(B(BK)(BKI))" *)

let _ = let module C = Conv0(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l7 ()
;;

(* - : ('_a -> '_b -> '_c -> '_a) PSKI.repr = "B(B(BI))(B(BK)(BKI))" *)

let 1 = let module C = Conv0(RSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l7 ()) 1 2 3
;;


let _ = let module C = Conv0(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l8 ()
;;

(*
 - : (('_a -> '_b -> '_c) -> ('_a -> '_b) -> '_a -> '_c) PSKI.repr =
"CC(CCI(BS(BKI)))(BS(B(BS)(B(CCI)(B(BS)(B(BK)(BKI))))))"
*)

let 3 = let module C = Conv0(RSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l8 ()) (+) succ 1
;;

let _ = let module C = Conv0(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.bad2 ()
;;

(* - : ('_a -> ('_a -> '_b) -> '_b) PSKI.repr = "B(SI)(BKI)" *)

let _ = let module C = Conv0(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.bad3 ()
;;

(*
- : ('_a -> '_b -> ('_b -> '_a -> '_c) -> '_c) PSKI.repr =
"B(S(BS(B(SI)(BKI))))(B(BK)(BKI))"
*)

let _ = let module C = Conv0(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.bad4 ()

(*
 - : ('_a -> '_b -> '_c -> ('_c -> '_b -> '_a -> '_d) -> '_d) PSKI.repr =
"B(S(BS(B(BS)(B(S(BS(B(SI)(BKI))))(B(BK)(BKI))))))(B(B(BK))(B(BK)(BKI)))"
*)


(* ------------------------------------------------------------------------
 More optimal translation 
*)
module Conv(S:SKI) (* : Lam *) = struct
  (* Generally open code with variables x0 x1 ... xn where
     x has the index 0
     is represented as
     D xn ... x0 where D is closed
     If a term does not have a variable with index 0 as
     free, we add it, using combinators

    Variables are eliminated by eta-reduction
   *)
  (* A generally open expression *)
  type ('g,'a) repr =
    | C: 'a S.repr -> ('g,'a) repr   (* closed code *)
    | N: ('g,'a->'b) repr -> ('a*'g,'b) repr  (* N e === (s e) z *)
    | W: ('g,'a) repr -> (_*'g,'a) repr  (* weakened: W e === K e *)

  let z:   ('a*'g,'a) repr = N (C S.kI)
  let s:   ('b*'g,'a) repr -> (_*('b*'g),'a) repr = fun e -> W e

  let rec ($$): type g a b. (g,a->b) repr -> (g,a) repr -> (g,b) repr = 
   fun e1 e2 ->
    match (e1,e2) with
    | (W e1, W e2)      -> W (e1 $$ e2)          (* both weakened *)
    | (W e, C d)        -> W (e $$ C d)
    | (C d, W e)        -> W (C d $$ e)
    (* (K (e1 xm ... x1) (e2 xn ... x1 x0) 
       == (e1 xm ... x1) ((e2 xn ... x1) x0)
       == B (e1 xm ... x1) (e2 xn ... x1) x0
    *)
    | (W e1, N e2)      -> N ((C S.kB) $$ e1 $$ e2)
    (* Mirror image *)
    | (N e1, W e2)      -> N ((C S.kC) $$ e1 $$ e2)
    (* (e1 x0) (e2 x0) == S e1 e2 x0 *)
    | (N e1, N e2)      -> N ((C S.kS) $$ e1 $$ e2)

    | (C d, N e)        -> N (C S.(kB $! d) $$ e)
    (* C C f g x --> C g f x --> g x f *)
    (* | (N e, C d)        -> N ((C S.kC) $$ e $$ C d)  below is better *)
    | (N e, C d)        -> N (C S.(kC $! kC $! d) $$ e)
    | (C d1, C d2)      -> C (S.(d1 $! d2))

  let lam: ('a*'g,'b) repr -> ('g,'a->'b) repr = function
    | C d -> C (S.(kK $! d))
    | N e -> e                          (* eta-contraction *)
    | W e -> (C S.kK) $$ e

  let observe : (unit,'a) repr -> 'a S.repr = function
  (C d) -> d

end
;;

let _ = let module C = Conv(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l1 ()
;;
(* - : ('_a -> '_a) PSKI.repr = "I" *)

let _ = let module C = Conv(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l2 ()
;;
(*  - : ('_a -> '_b -> '_b) PSKI.repr = "KI" *)

let _ = let module C = Conv(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l3 ()
;;
(* - : ('_a -> '_b -> '_a) PSKI.repr = "BKI" *)

let 1 = let module C = Conv(RSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l3 ()) 1 2
;;

let _ = let module C = Conv(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l4 ()
;;

(* old:  - : (('_a -> '_b) -> '_a -> '_b) PSKI.repr = "C(BBI)I" *)

(*  - : (('_a -> '_b) -> '_a -> '_b) PSKI.repr = "CCI(BBI)" *)

let 5 = let module C = Conv(RSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l4 ()) succ 4
;;

let _ = let module C = Conv(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l5 ()
;;
(*
  - : ('_a -> ('_a -> '_b) -> '_b) PSKI.repr = "B(CI)I"
*)


let 5 = let module C = Conv(RSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l5 ()) 4 succ
;;


let _ = let module C = Conv(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l6 ()
;;

(*  - : ('_a -> '_b -> ('_a -> '_c) -> '_c) PSKI.repr = "BK(B(CI)I)" *)

let _ = let module C = Conv(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l7 ()
;;

(* - : ('_a -> '_b -> '_c -> '_a) PSKI.repr = "BK(BK(BII))" *)

let 1 = let module C = Conv(RSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l7 ()) 1 2 3
;;


let _ = let module C = Conv(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l8 ()
;;

(*
  - : (('_a -> '_b -> '_c) -> ('_a -> '_b) -> '_a -> '_c) PSKI.repr =
"CC(CCI(BBI))(BB(BS(CCI(BBI))))"
*)

let 3 = let module C = Conv(RSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l8 ()) (+) succ 1
;;

let _ = let module C = Conv(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.bad2 ()
;;

(* - : ('_a -> ('_a -> '_b) -> '_b) PSKI.repr = "B(CI)I" *)

let _ = let module C = Conv(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.bad3 ()
;;

(*  - : ('_a -> '_b -> ('_b -> '_a -> '_c) -> '_c) PSKI.repr =
"B(C(BC(B(CI)I)))I"
*)

let _ = let module C = Conv(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.bad4 ()

(*
- : ('_a -> '_b -> '_c -> ('_c -> '_b -> '_a -> '_d) -> '_d) PSKI.repr =
"B(C(BC(B(BC)(B(C(BC(B(CI)I)))I))))I"
*)

(* A bit more optimal compilation scheme ... *)


module Conv2(S:SKI) (* : Lam *) = struct
  (* Generally open code with variables x0 x1 ... xn where
     x has the index 0
     is represented as
     D xn ... x0 where D is closed
     If a term does not have a variable with index 0 as
     free, we add it, using combinators

    Variables are eliminated by eta-reduction
   *)
  (* A generally open expression *)
  type ('g,'a) repr =
    | C: 'a S.repr -> ('g,'a) repr   (* closed code *)
    | V: ('a*'g,'a) repr             (* reference to the top env variable *)
    | N: ('g,'a->'b) repr -> ('a*'g,'b) repr  (* N e === (s e) z *)
    | W: ('g,'a) repr -> (_*'g,'a) repr  (* weakened: W e === K e *)

  let z:   ('a*'g,'a) repr = V
  let s:   ('b*'g,'a) repr -> (_*('b*'g),'a) repr = fun e   -> W e

  let rec ($$): type g a b. (g,a->b) repr -> (g,a) repr -> (g,b) repr = 
   fun e1 e2 ->
    match (e1,e2) with
    | (W e1, W e2)      -> W (e1 $$ e2)          (* both weakened *)
    | (W e, C d)        -> W (e $$ C d)
    | (C d, W e)        -> W (C d $$ e)
    | (W e,V)           -> N e                   (* e x *)
    | (V, W e)          -> N (C (S.(kC $! kI)) $$ e)
    (* (K (e1 xm ... x1) (e2 xn ... x1 x0) 
       == (e1 xm ... x1) ((e2 xn ... x1) x0)
       == B (e1 xm ... x1) (e2 xn ... x1) x0
    *)
    | (W e1, N e2)      -> N ((C S.kB) $$ e1 $$ e2)
    (* Mirror image *)
    | (N e1, W e2)      -> N ((C S.kC) $$ e1 $$ e2)
    (* (e1 x0) (e2 x0) == S e1 e2 x0 *)
    | (N e1, N e2)      -> N ((C S.kS) $$ e1 $$ e2)
    (* e x x *)
    | (N e, V)          -> N (C S.kS $$ e $$ C S.kI)
    (* x (e x) *)
    | (V, N e)          -> N (C S.(kS $! kI) $$ e)
     
    | (C d, N e)        -> N ((C S.(kB $! d)) $$ e)
    | (C d, V)          -> N (C d)                    (* d x *)
    | (V, C d)          -> N (C S.(kC $! kI $! d))    (* x d *)
    (* x x, can't actually happen for simple types *)
    | (V,V)             -> failwith "can't happen for simple types" (* N (C S.(kS $! kI $! kI)) *)
    (* C C f g x --> C g f x --> g x f *)
    (* | (N e, C d)        -> N ((C S.kC) $$ e $$ C d)  below is better *)
    | (N e, C d)        -> N ((C S.(kC $! kC $! d)) $$ e)
    | (C d1, C d2)      -> C (S.(d1 $! d2))

  let lam: type a b g. (a*g,b) repr -> (g,a->b) repr = function
    | V   -> C S.kI
    | C d -> C (S.(kK $! d))
    | N e -> e                          (* eta-contraction *)
    | W e -> (C S.kK) $$ e

  let observe : (unit,'a) repr -> 'a S.repr = function
  (C d) -> d

end
;;

let _ = let module C = Conv2(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l1 ()
;;
(* - : ('_a -> '_a) PSKI.repr = "I" *)

let _ = let module C = Conv2(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l2 ()
;;
(*  - : ('_a -> '_b -> '_b) PSKI.repr = "KI" *)

let _ = let module C = Conv2(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l3 ()
;;
(* - : ('_a -> '_b -> '_a) PSKI.repr = "K" *)

let 1 = let module C = Conv2(RSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l3 ()) 1 2
;;

let _ = let module C = Conv2(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l4 ()
;;

(*   - : (('_a -> '_b) -> '_a -> '_b) PSKI.repr = "I" *)

let 5 = let module C = Conv2(RSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l4 ()) succ 4
;;

let _ = let module C = Conv2(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l5 ()
;;
(*
  - : ('_a -> ('_a -> '_b) -> '_b) PSKI.repr = "CI"
*)


let 5 = let module C = Conv2(RSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l5 ()) 4 succ
;;


let _ = let module C = Conv2(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l6 ()
;;

(* - : ('_a -> '_b -> ('_a -> '_c) -> '_c) PSKI.repr = "BK(CI)" *)

let _ = let module C = Conv2(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l7 ()
;;

(*
- : ('_a -> '_b -> '_c -> '_a) PSKI.repr = "BK(BKI)"
*)

let 1 = let module C = Conv2(RSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l7 ()) 1 2 3
;;


let _ = let module C = Conv2(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l8 ()
;;

(*
- : (('_a -> '_b -> '_c) -> ('_a -> '_b) -> '_a -> '_c) PSKI.repr = "S"
*)

let 3 = let module C = Conv2(RSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l8 ()) (+) succ 1
;;

let _ = let module C = Conv2(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.bad2 ()
;;

(* - : ('_a -> ('_a -> '_b) -> '_b) PSKI.repr = "CI" *)

let _ = let module C = Conv2(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.bad3 ()
;;

(* - : ('_a -> '_b -> ('_b -> '_a -> '_c) -> '_c) PSKI.repr = "C(BC(CI))" *)

let _ = let module C = Conv2(PSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.bad4 ()

(*
 - : ('_a -> '_b -> '_c -> ('_c -> '_b -> '_a -> '_d) -> '_d) PSKI.repr =
"C(BC(B(BC)(C(BC(CI)))))"
*)


(*
 * ------------------------------------------------------------------------
 * Practical extensions
 *)

(* Extension of BigLam with more constants *)
module type BigLam = sig
  include Lam

  val int:  int -> ('g,int) repr
  val bool: bool -> ('g,bool) repr

  val add: ('g,int->int->int) repr
  val sub: ('g,int->int->int) repr
  val mul: ('g,int->int->int) repr
  val div: ('g,int->int->int) repr
  val rem: ('g,int->int->int) repr

  val eq:  ('g,'a->'a->bool) repr
  val if_: ('g,bool->'a->'a->'a) repr

  val fix: ('g, ('a->'a)->'a) repr
end

module BigEx(S:BigLam) = struct
  open S
  (* ((\x. + x x) 5), SLPJ book, PDF p. 277 *)
  let a5 () = (lam (add $$ z $$ z)) $$ int 5

  let fact () = fix $$ lam (lam
    (if_ $$ (eq $$ z $$ int 0) $$ int 1
         $$ (mul $$ z $$ (s z $$ (sub $$ z $$ int 1)))))

  (* The gcd of two integers a and b where b <= a. 
     The example from 16.2.6 of SPJ Book, p. 287 *)
  let gcd () = fix $$ lam (lam (lam
    (let self = s (s z) and a = s z and b = z in
     if_ $$ (eq $$ int 0 $$ b) $$ a
         $$ (self $$ b $$ (rem $$ a $$ b)))))
 
end

module type BigSKI = sig
  include SKI

  val int:  int  -> int repr
  val bool: bool -> bool repr

  val add:  (int->int->int) repr
  val sub:  (int->int->int) repr
  val mul:  (int->int->int) repr
  val div:  (int->int->int) repr
  val rem:  (int->int->int) repr

  val eq:   ('a->'a->bool) repr
  val if_:  (bool->'a->'a->'a) repr

  val fix:  (('a->'a)->'a) repr
end

module PBigSKI = struct
  include PSKI

  let int:  int  -> int repr = fun i -> parens true @@ string_of_int i
  let bool: bool -> bool repr = function
    | true  -> "(true)"
    | false -> "(false)"

  let add:  (int->int->int) repr = "(+)"
  let sub:  (int->int->int) repr = "(-)"
  let mul:  (int->int->int) repr = "(*)"
  let div:  (int->int->int) repr = "(/)"
  let rem:  (int->int->int) repr = "Rem"

  let eq:   ('a->'a->bool) repr  = "(=)"
  let if_:  (bool->'a->'a->'a) repr = "IF"

  let fix:  (('a->'a)->'a) repr = "Y"
end

(* The evaluator that implements head-first reductions. Now we have to
   be careful: with fix, the divergence is possible.
*)
module RBigSKI = struct
  type 'a repr =
    | B: 'a -> 'a repr                  (* constants, strict functions  *)
    | F: ('a repr -> 'b repr) -> ('a->'b) repr   (* possibly non-strict *)
    | A: ('a->'b) repr * 'a repr -> 'b repr (* non-commited application *)

  let kI:  ('a->'a) repr     = F (fun x -> x)
  let kK:  ('a->'b->'a) repr = F (fun x -> F (fun y -> x))
  let kS:  (('a->'b->'c)->('a->'b)->'a->'c) repr = 
    F (fun f -> F (fun g -> F(fun x -> A(A(f,x),A(g,x)))))
  let kB:  (('a -> 'b) -> ('c -> 'a) -> 'c -> 'b) repr =
    F (fun f -> F (fun g -> F(fun x -> A(f,A(g,x)))))
  let kC:  (('a -> 'b -> 'c) -> ('b -> 'a -> 'c)) repr =
    F (fun f -> F (fun g -> F(fun x -> A(A(f,x),g))))
  let ($!): type a b. (a->b) repr -> a repr -> b repr = fun f x -> 
    match (f,x) with
    | (B f, B x) -> B (f x)             (* strict function *)
    | (F f, x)   -> f x
    | (f,x)      -> A(f,x)

  let int:  int  -> int repr  = fun x -> B x
  let bool: bool -> bool repr = fun x -> B x

  let add:  (int->int->int) repr = B ( + )
  let sub:  (int->int->int) repr = B ( - )
  let mul:  (int->int->int) repr = B ( * )
  let div:  (int->int->int) repr = B ( / )
  let rem:  (int->int->int) repr = B (fun  x y -> x mod y)

  let eq:   ('a->'a->bool) repr  = B ( = )

  let rec fix:  (('a->'a)->'a) repr = F(function
    | B _ -> failwith "<loop>"          (* fix of a strict function *)
    | f   -> A(f,A(fix,f)))

  let rec observe: type a. a repr -> a = function
    | B x -> x
    | F f -> fun x -> observe @@ f (B x)
    | A(B f,x)   -> f (observe x)       (* strict function *)
    | A(F f,x)   -> observe @@ f x
    | A(f,x)     -> observe @@ A (hnf f,x)
  and hnf: type a. a repr -> a repr = function
    | A(B f,x) -> B (f (observe x))
    | A(F f,x) -> hnf @@ f x
    | A(f,x)   -> hnf @@ A(hnf f,x)
    | x -> x

  let if_:  (bool->'a->'a->'a) repr = F(fun test -> F (fun th -> F(fun el ->
    let rec loop = function 
      | B true  -> th
      | B false -> el
      | test    -> A(F (fun x -> loop (hnf x)),test)
    in loop test)))
end


module BigConv2(S:BigSKI) (* : BigLam *) = struct
  (* A generally open expression *)
  type ('g,'a) repr =
    | C: 'a S.repr -> ('g,'a) repr   (* closed code *)
    | V: ('a*'g,'a) repr             (* reference to the top env variable *)
    | N: ('g,'a->'b) repr -> ('a*'g,'b) repr  (* N e === (s e) z *)
    | W: ('g,'a) repr -> (_*'g,'a) repr  (* weakened: W e === K e *)

  let z:   ('a*'g,'a) repr = V
  let s:   ('b*'g,'a) repr -> (_*('b*'g),'a) repr = fun e   -> W e

  let rec ($$): type g a b. (g,a->b) repr -> (g,a) repr -> (g,b) repr = 
   fun e1 e2 ->
    match (e1,e2) with
    | (W e1, W e2)      -> W (e1 $$ e2)          (* both weakened *)
    | (W e, C d)        -> W (e $$ C d)
    | (C d, W e)        -> W (C d $$ e)
    | (W e,V)           -> N e                   (* e x *)
    | (V, W e)          -> N (C (S.(kC $! kI)) $$ e)
    (* (K (e1 xm ... x1) (e2 xn ... x1 x0) 
       == (e1 xm ... x1) ((e2 xn ... x1) x0)
       == B (e1 xm ... x1) (e2 xn ... x1) x0
    *)
    | (W e1, N e2)      -> N ((C S.kB) $$ e1 $$ e2)
    (* Mirror image *)
    | (N e1, W e2)      -> N ((C S.kC) $$ e1 $$ e2)
    (* (e1 x0) (e2 x0) == S e1 e2 x0 *)
    | (N e1, N e2)      -> N ((C S.kS) $$ e1 $$ e2)
    (* e x x *)
    | (N e, V)          -> N (C S.kS $$ e $$ C S.kI)
    (* x (e x) *)
    | (V, N e)          -> N (C S.(kS $! kI) $$ e)
     
    | (C d, N e)        -> N ((C S.(kB $! d)) $$ e)
    | (C d, V)          -> N (C d)                    (* d x *)
    | (V, C d)          -> N (C S.(kC $! kI $! d))    (* x d *)
    (* x x, can't actually happen for simple types *)
    | (V,V)             -> failwith "can't happen for simple types" (* N (C S.(kS $! kI $! kI)) *)
    (* C C f g x --> C g f x --> g x f *)
    (* | (N e, C d)        -> N ((C S.kC) $$ e $$ C d)  below is better *)
    | (N e, C d)        -> N ((C S.(kC $! kC $! d)) $$ e)
    | (C d1, C d2)      -> C (S.(d1 $! d2))

  let lam: type a b g. (a*g,b) repr -> (g,a->b) repr = function
    | V   -> C S.kI
    | C d -> C (S.(kK $! d))
    | N e -> e                          (* eta-contraction *)
    | W e -> (C S.kK) $$ e

  let observe : (unit,'a) repr -> 'a S.repr = function
  (C d) -> d

  let int:  int -> ('g,int) repr   = fun x -> C S.(int x)
  let bool: bool -> ('g,bool) repr = fun x -> C S.(bool x)

  let add: ('g,int->int->int) repr = C S.add
  let sub: ('g,int->int->int) repr = C S.sub
  let mul: ('g,int->int->int) repr = C S.mul
  let div: ('g,int->int->int) repr = C S.div
  let rem: ('g,int->int->int) repr = C S.rem

  let eq:  ('g,'a->'a->bool) repr  = C S.eq
  let if_: ('g,bool->'a->'a->'a) repr = C S.if_

  let fix: ('g, ('a->'a)->'a) repr = C S.fix
end



let _ = let module C = BigConv2(PBigSKI) in
        let module M = BigEx(C) in
        C.observe @@ M.a5 ()

(* - : int PBigSKI.repr = "S((+))I((5))" *)

(* In SLPG Book:
((\x. + x x) 5) ===
S (S (K +) I) I 5
But with optimizations, it is just S + I 5
*)

let 10 = let module C = BigConv2(RBigSKI) in
        let module M = BigEx(C) in
        RBigSKI.observe @@ C.observe @@ M.a5 ()


let _ = let module C = BigConv2(PBigSKI) in
        let module M = BigEx(C) in
        C.observe @@ M.fact ()

(*
    - : (int -> int) PBigSKI.repr =
"Y(B(S(CC((1))(B(IF)(CC((0))((=))))))(B(S(( * )))(CC(CC((1))((-)))B)))"
*)

let 120 = let module C = BigConv2(RBigSKI) in
        let module M = BigEx(C) in
        (RBigSKI.observe @@ C.observe @@ M.fact ()) 5

let _ = let module C = BigConv2(PBigSKI) in
        let module M = BigEx(C) in
        C.observe @@ M.gcd ()

(*
  - : (int -> int -> int) PBigSKI.repr =
"Y(B(S(BS(C(B(IF)((=)((0)))))))(CC(Rem)(BBS)))"
*)

let 7 = let module C = BigConv2(RBigSKI) in
        let module M = BigEx(C) in
        (RBigSKI.observe @@ C.observe @@ M.gcd ()) 35 14

(*
 * ========================================================================
 * Linear-time translation
 *)


(* Generalized versions of K, B, C, S combinators, dealing with n
   arguments
*)
module type BulkSKI = sig
  include SKI
  type u                                (* unitype *)

  (* B_n f g dn ... d1 --> f (g dn ... d1) *)
  val kBn: int -> u repr
  (* C_n f g dn ... d1 --> f dn ... d1 g *)
  val kCn: int -> u repr
  (* S_n f g dn ... d1 --> (f dn ... d1) (g dn ... d1) *)
  val kSn: int -> u repr

  val ($?): u repr -> u repr -> u repr

  val uclose: 'a repr -> u repr        (* univ injection *)
  val uopen:  u repr -> 'a repr        (* univ projection: careful! *)
end

let iterate : int -> ('a -> 'a) -> 'a -> 'a list = fun n f z ->
  let rec loop last acc = function
    | 0 -> List.rev acc
    | 1 -> List.rev @@ last :: acc
    | n -> loop (f last) (last :: acc) (n-1)
  in loop z [] n

let [1;2;3;4;5] = iterate 5 succ 1;;

module RBulkSKI = struct
  include RSKI

  type u = U : 'a -> u

  let uclose: 'a repr -> u repr = fun x -> U x

  let uopen: u repr -> 'a repr          (* univ projection: careful! *)
      = function U d -> Obj.magic d

  let mapU : ('a -> 'b) -> u -> u =      (* a safer alternative *)
   fun f -> fun u -> U (f (uopen u))

  let ($?) u1 u2 = uclose (uopen u1 @@ uopen u2)

  (* Primed combinators *)
  let kK' : (('a -> 'b) -> ('w -> 'a) -> 'w -> 'b) repr = kB

  (* S' t a b x = t (a x) (b x);; *)
  let kS' : 
      (('a -> 'b -> 'c) -> ('d -> 'a) -> ('d -> 'b) -> 'd -> 'c) repr =
   kB $! (kB $! kS) $! kB

  (* B' t a b x = t a (b x);; *)
  let kB' : (('a -> 'b -> 'c) -> 'a -> ('d -> 'b) -> 'd -> 'c) repr =
    kB $! kB

  (* C' t a b x = t (a x) b;; *)
  let kC' : (('a -> 'b -> 'c) -> ('d -> 'a) -> 'b -> 'd -> 'c) repr =
   kB $! (kB $! kC) $! kB

  let max_depth = 10 (* We pre-compute all combinators to that depth,
                        for simplicity. In production, just use flexible arrays:
                        that is, reallocate to the twice the current size when
                        about to overflow. For now, we skip the reallocation *)

  (* The 0th element is K1 *)
  let kKs = Array.of_list @@ 
              iterate max_depth (mapU (fun d -> kK' $! d)) (U kK)

  let kSs = Array.of_list @@ 
              iterate max_depth (mapU (fun d -> kS' $! d)) (U kS)

  let kBs = Array.of_list @@ 
              iterate max_depth (mapU (fun d -> kB' $! d)) (U kB)

  let kCs = Array.of_list @@ 
              iterate max_depth (mapU (fun d -> kC' $! d)) (U kC)

  let kKn i = kKs.(i-1)
  let kSn i = kSs.(i-1)
  let kBn i = kBs.(i-1)
  let kCn i = kCs.(i-1)
end


module PBulkSKI = struct
  include PSKI
  type u = string

  let kSn i = "S" ^ string_of_int i
  let kBn i = "B" ^ string_of_int i
  let kCn i = "C" ^ string_of_int i

  let ($?) = ($!)
  let uclose x = x
  let uopen  x = x
end


module LinearConv(S:BulkSKI) (* : Lam *) = struct
  type ('g,'a) repr =
    | C: 'a S.repr -> ('g,'a) repr   (* closed code *)
    | N: S.u S.repr * int -> ('g,'a) repr

  let ($$): type g a b. (g,a->b) repr -> (g,a) repr -> (g,b) repr = 
   fun x y -> match (x,y) with
    | (C d1,C d2)     -> C (S.(d1 $! d2))
    | (C d1,N (d2,l)) -> N (S.(kBn l $? uclose d1 $? d2),l)  (* D1 (D2 x) *)
    | (N (d1,l),C d2) -> N (S.(kCn l $? d1 $? uclose d2),l)  (* (D1 x) D2 *)
    | (N (d1,l),N (d2,l2)) when l = l2 -> 
        N (S.(kSn l $? d1 $? d2),l)  (* (D1 x) (D2 x) *)
    | (N (d1,l1),N (d2,l2)) when l1 < l2 -> 
        let k = l2 - l1 in
        N (S.(kBn k $? (kSn l1 $? d1) $? d2),l2)
    | (N (d1,l1),N (d2,l2)) (* when l1 > l2 *) -> 
        let k = l1 - l2 in
        let d1' = S.(kBn k $? kSn l2 $? d1) in
        N (S.(kCn k $? d1' $? d2), l1)
 
  let uI = S.(uclose kI)                (* for the sake of polymorphism in z *)
  let z:   ('a*'g,'a) repr = N (uI, 1)
  let s:   ('b*'g,'a) repr -> (_*('b*'g),'a) repr = fun e ->
    let N (d,l) = (C S.kK) $$ e in N (d,l+1)

  let lam: type a g b. (a*g,b) repr -> (g,a->b) repr = function
    | C k        -> C (S.(kK $! k))
    | N (d,1)    -> C (S.uopen d)
    | N (d,l)    -> N (d,l-1)

  let observe : (unit,'a) repr -> 'a S.repr = function
    | C d -> d
    | _   -> failwith "impossible"
end

let 2 = let module M = Ex1(SizeLam) in M.l1 ();;
let _ = let module C = LinearConv(PBulkSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l1 ()
;;

(* - : ('_a -> '_a) PBulkSKI.repr = "I" *)

let 1 = let module C = LinearConv(RBulkSKI) in
        let module M = Ex1(C) in
        C.observe (M.l1 ()) 1
;;


let 3 = let module M = Ex1(SizeLam) in M.l2 ();;
let _ = let module C = LinearConv(PBulkSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l2 ()
;;

(*  - : ('_a -> '_b -> '_b) PSKI.repr = "KI" *)

let 4 = let module C = LinearConv(RBulkSKI) in
        let module M = Ex1(C) in
        C.observe (M.l2 ()) 1 4
;;

let 4 = let module M = Ex1(SizeLam) in M.l3 ();;
let _ = let module C = LinearConv(PBulkSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l3 ()
;;

(* - : ('_a -> '_b -> '_a) PSKI.repr = "B1KI" *)

let 1 = let module C = LinearConv(RBulkSKI) in
        let module M = Ex1(C) in
        C.observe (M.l3 ()) 1 4
;;

let 6 = let module M = Ex1(SizeLam) in M.l4 ();;
let _ = let module C = LinearConv(PBulkSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l4 ()
;;

(* - : (('_a -> '_b) -> '_a -> '_b) PBulkSKI.repr = "C1(B1(S1)(B1KI))I" *)

let 5 = let module C = LinearConv(RBulkSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l4 ()) succ 4
;;

let 6 = let module M = Ex1(SizeLam) in M.l5 ();;
let _ = let module C = LinearConv(PBulkSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l5 ()
;;

(* - : ('_a -> ('_a -> '_b) -> '_b) PBulkSKI.repr = "B1(S1I)(B1KI)" *)

let 5 = let module C = LinearConv(RBulkSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l5 ()) 4 succ
;;

let 8 = let module M = Ex1(SizeLam) in M.l6 ();;
let _ = let module C = LinearConv(PBulkSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l6 ()
;;

(* 
- : ('_a -> '_b -> ('_a -> '_c) -> '_c) PBulkSKI.repr = "B2(S1I)(B2K(B1KI))"
*)

let 9 = let module M = Ex1(SizeLam) in M.l7 ();;
let _ = let module C = LinearConv(PBulkSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l7 ()
;;

(* - : ('_a -> '_b -> '_c -> '_a) PBulkSKI.repr = "B3I(B2K(B1KI))" *)

let 1 = let module C = LinearConv(RBulkSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l7 ()) 1 2 3
;;

let 13 = let module M = Ex1(SizeLam) in M.l8 ();;
let _ = let module C = LinearConv(PBulkSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.l8 ()
;;

(* 19 combinators *)
(*
  - : (('_a -> '_b -> '_c) -> ('_a -> '_b) -> '_a -> '_c) PBulkSKI.repr =
"C1(B1(S2)(C2(B2(S1)(B2K(B1KI)))I))(C1(B1(S1)(B1KI))I)"
*)


let 3 = let module C = LinearConv(RBulkSKI) in
        let module M = Ex1(C) in
        (C.observe @@ M.l8 ()) (+) succ 1
;;


let 6 = let module M = Ex1(SizeLam) in M.bad2 ();;
let _ = let module C = LinearConv(PBulkSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.bad2 ()
;;

(* 6 combinators *)
(* - : ('_a -> ('_a -> '_b) -> '_b) PBulkSKI.repr = "B1(S1I)(B1KI)"
*)

let 11 = let module M = Ex1(SizeLam) in M.bad3 ();;
let _ = let module C = LinearConv(PBulkSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.bad3 ()
;;

(* 13 combinators *)
(*
  - : ('_a -> '_b -> ('_b -> '_a -> '_c) -> '_c) PBulkSKI.repr =
"B1(S2(B1(S1I)(B1KI)))(B2K(B1KI))"
*)


let 17 = let module M = Ex1(SizeLam) in M.bad4 ();;

let _ = let module C = LinearConv(PBulkSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.bad4 ()
;;

(* 22 combinators *)
(*
  - : ('_a -> '_b -> '_c -> ('_c -> '_b -> '_a -> '_d) -> '_d) PBulkSKI.repr =
"B1(S3(B1(S2(B1(S1I)(B1KI)))(B2K(B1KI))))(B3K(B2K(B1KI)))"
*)


let 17 = let module M = Ex1(SizeLam) in M.nbad4 ();;

let _ = let module C = LinearConv(PBulkSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.nbad4 ()
;;
(* 22 combinators *)
(*
  - : ('_a -> '_b -> ('_a -> '_c) -> ('_b -> '_c -> '_d) -> '_d) PBulkSKI.repr
= "B1(S3(B2(S1I)(B2K(B1KI))))(B2(S2(B1KI))(B3K(B2K(B1KI))))"
*)


let 51 = let module M = Ex1(SizeLam) in M.nbad8 ();;

let _ = let module C = LinearConv(PBulkSKI) in
        let module M = Ex1(C) in
        C.observe @@ M.nbad8 ()
;;
(* 78 combinators *)
(*
  - : ('_a ->
     '_b ->
     '_c ->
     '_d ->
     ('_a -> '_e) ->
     ('_b -> '_f) -> ('_c -> '_e -> '_g) -> ('_d -> '_f -> '_g -> '_h) -> '_h)
    PBulkSKI.repr
=
"B1(S7(B2(S5(B4(S1I)(B4K(B3K(B2K(B1KI))))))(B4(S3(B2K(B1KI)))(B6K(B5K(B4K(B3K(B2K(B1KI)))))))))(B2(S6(B4(S2(B1KI))(B5K(B4K(B3K(B2K(B1KI)))))))(B4(S4(B3K(B2K(B1KI))))(B7K(B6K(B5K(B4K(B3K(B2K(B1KI)))))))))"
*)

