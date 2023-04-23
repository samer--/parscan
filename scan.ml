module type MONOID = sig
  type t
  val zero: t
  val add: t -> t -> t
end

module type FUNCTOR = sig
  type 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
end

(* basic utilities *)
let id x = x
let (%>) f g x = g (f x)
let (%)  f g x = f (g x)
let ffst f (x,y) = (f x, y)
let fsnd f (x,y) = (x, f y)
let assocl (a,(b,c)) = (a,b), c
let swap (x,y) = (y,x)
let prod f g (x, y) = (f x, g y)
let curry f x y = f (x, y)

type 'a pair = 'a * 'a

module Pair = struct
  type 'a t = 'a pair

  let map f (x1,x2) = f x1, f x2
  let unzip (((x1,y1), (x2,y2)) : ('a * 'b) t): 'a t * 'b t  = (x1,x2), (y1,y2)
  let unzip_with f = unzip % map f
  let zip_with : ('a -> 'b -> 'c) -> 'a t * 'b t -> 'c t =
    fun f ((x1,x2), (y1,y2)) -> (f x1 y1, f x2 y2)

  let scan : type a. (module MONOID with type t=a) -> a t -> a t * a
    = fun (module M) (x1,x2) -> (M.zero,x1), M.add x1 x2
end

module PairM (M: MONOID) = struct
  (* Pair but with scan bound to the given monoid as a first class module *)
  include Pair
  let scan = scan (module M)
end

(* This part provides operation counting as an effect by using delimited continuations *)
(* -- universal type, taken from Filinski -- *)
module Dynamic = struct
  exception Dynamic
  type t = Dyn of (unit->unit)

  let newdyn () : ('a -> t) * (t -> 'a) =
    let r = ref None in
    ( (fun a -> Dyn (fun () -> r := Some a)),
      (fun (Dyn d) -> r := None; d ();
                      match !r with
                      | Some a -> a
                      | None -> raise Dynamic))
end

module NoisyInt = struct
  (* It's noisy because it counts the number of additions performed *)
  open Delimcc

  type t = int
  let zero = 0
  let p = new_prompt ()

  let add x y = shift0 p (fun k -> fsnd ((+) 1) (k ())); x + y

  let counting_adds f =
    let ind, outd = Dynamic.newdyn() in
    ffst outd @@ push_prompt p @@ fun () -> (ind (f ()), 0)
end

(* ----------------------------------------------------------------------*)

(* boring old binary tree *)

module Tree = struct
  type 'a t = | L of 'a | B of 'a t * 'a t
  let rec map (f: 'a -> 'b): 'a t -> 'b t = function
    | L x -> L (f x)
    | B (a,b) -> B (map f a, map f b)
end

(* Different forms of exclusive left scan *)


module Scan1 (M: MONOID) = struct
  open Tree

  let rec scan : M.t Tree.t -> M.t Tree.t * M.t = function
    | L x -> L M.zero, x
    | B (a, b) ->
        let (a', at), (b', bt) = (scan a, scan b) in
        B (a', Tree.map (M.add at) b'), (M.add at bt)

  let iota n : int Tree.t =
    let rec iota' m =
      match m with
        | 0 -> (L 1, 1)
        | n -> let t, b = iota' (n-1) in (B (t, Tree.map ((+) b) t), 2*b)
    in fst (iota' n)
end

module Scan2 (M: MONOID) = struct
  open Tree
  let rec scan : M.t pair Tree.t -> M.t pair Tree.t * M.t = function
    | L (x, y) -> L (M.zero, x), (M.add x y)
    | B (a, b) ->
      let a', at = scan a in
      let b', bt = scan b in
      B (a', Tree.map (Pair.map (M.add at)) b'), (M.add at bt)

  let iota n : int Pair.t Tree.t = (* but no partridge - harr harr *)
    let rec iota' m =
      match m with
        | 0 -> (L (1,2), 2)
        | n -> let t, b = iota' (n-1) in (B (t, Tree.map (Pair.map ((+) b)) t), 2*b)
    in fst (iota' (n - 1))
end

(* -----------------------------------------------------------------------*)

module TopDown (M: MONOID) = struct
  module P = PairM (M)
  module T = struct
    type 'a t =
      | L of 'a
      | B of ('a t P.t)

    let rec map (f: 'a -> 'b): 'a t -> 'b t = function
      | L x -> L (f x)
      | B tp -> B (P.map (map f) tp)
  end

  let rec scan : M.t T.t -> M.t T.t * M.t =
    let branch tp = T.B tp in
    let combine = branch % P.zip_with (T.map % M.add) % swap in function
    | T.B tp -> ffst combine % assocl % fsnd P.scan % P.unzip_with scan @@ tp
    | T.L x -> T.L M.zero, x

  let iota n : int T.t =
    let rec iota' m =
      match m with
      | 0 -> (T.L 1, 1)
      | n -> let t, b = iota' (n-1) in (T.B (t, T.map ((+) b) t), 2*b)
    in fst (iota' n)
end

module BottomUp (M: MONOID) = struct
  module P = PairM (M)
  module T = struct
    type 'a t =
      | L of 'a
      | B of ('a P.t t)

    let rec map : type a b. (a -> b) -> a t -> b t = fun f -> function
      | L x -> L (f x)
      | B t -> B (map (P.map f) t)

    let rec zip_with : type a b c. (a -> b -> c) -> a t * b t -> c t = fun f -> function
      | (L x, L y) -> L (f x y)
      | (B a, B b) -> B (zip_with (curry (P.zip_with f)) (a, b))
      | _ -> assert false

    let rec unzip_with : type a b c. (a -> b * c) -> a t -> b t * c t =
      let leaf x = L x in
      let branch t = B t in
      fun f -> function
      | L x -> (prod leaf leaf) (f x)
      | B t -> (prod branch branch) (unzip_with (P.unzip_with f) t)

  end

  let rec scan : M.t T.t -> M.t T.t * M.t =
    let branch tp = T.B tp in
    let combine = branch % T.zip_with (P.map % M.add) % swap in function
    | T.L x -> T.L M.zero, x
    | T.B t -> ffst combine % assocl % fsnd scan % T.unzip_with P.scan @@ t
end

(* ---------------------------------------------------------------------
 * Here we do some tricksy stuff in order to get the depth of the tree into
 * its type as a phantom type parameter.
 *)

(* Type level naturals *)
type z
type 'a suc = S of 'a (* don't understand why we need a constructor *)

(* Type AND value level naturals *)
type 'n nat =
  | Zero : z nat
  | Succ : 'n nat -> 'n suc nat


(* A binary tree whose depth is determined by a type level
 * natural. We don't need nat as we don't need to match on
 * the natural number if we have an actual tree to match on.
 *)
type ('d,'a) dtree =
  | LL : 'a -> (z,'a) dtree
  | BB : ('d,'a) dtree * ('d,'a) dtree -> ('d suc, 'a) dtree

let rec dtmap : type d. ('a -> 'b) -> (d,'a) dtree -> (d,'b) dtree =
  fun f -> function
    | LL x -> LL (f x)
    | BB (a,b) -> BB (dtmap f a, dtmap f b)

let rec diota : type d. d nat -> (d, int) dtree * int = function
  | Zero -> (LL 1, 1)
  | Succ n -> let t, b = diota n in (BB (t, dtmap ((+) b) t), 2*b)

let ( ~~ ) x = Succ x

module ScanD (M: MONOID) = struct
  open M
  type 'd t = ('d, M.t) dtree

  let rec scan : type d. d t -> d t * M.t = function
    | LL x -> LL zero, x
    | BB (a, b) ->
      let a', at = scan a in
      let b', bt = scan b in
      BB (a', dtmap (add at) b'), (add at bt)
end

(* ------------------------------------------------------- *)

module Scan1Int  = Scan1(Int)
module Scan2Int  = Scan2(Int)
module NScan1Int = Scan1(NoisyInt)
module NScan2Int = Scan2(NoisyInt)
module ScanDInt  = ScanD(Int)
