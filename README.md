# parscan
Investigation of parallel(isable) scans

This repo contains implementations of some of the ideas in Conal Elliot's
talk 'Can Tensor Programming Be Liberated from the Fortran Data Paradigm?'

    https://www.youtube.com/watch?v=oaIMMclGuog

The running example through this talk is the 'exclusive left scan', ie building
a running total of the numbers in a sequence, such as the first element of the
result is always 0 and the resulting structure is the same size and shape as the
input, and does NOT include the sum of all the elements (hence exclusive).

Conal quickly generalises this into a more composable form where the total is 
returned separately, so that the abstract type of the scan over some container
type constructor $C$ is, in Haskell-ish notation 
```
    Monoid A => C A -> (C A, A)
```
The talk looks at how the idea of scanning can be generalised from the familiar 
(sequential) algorithm for scanning a list to more parallelisable structures for
containter types built from different combinations of functors. He starts by 
looking at some rather complex and impenetrable looking UDA code for multithreaded 
scan and works towards obtaining a much cleaner expression of the underlying idea.
    
There are versions in O'Caml, Agda and Haskell.

## Agda version

See `agda` subdirectory.

### First try
Load `scan.agda` into an editor with Agda integration, eg a properly set-up
vim or emacs. Then, you can try reducing various scans to normal form. I use
vim with the `agda-vim` package from `derekelkins/agda-vim`. The binding
`<leader>n` prompts for an expression to evaluate. For example:
`let open Direct in iota 3` builds a depth 3 tree containing the natural numbers
1 to 2^3, ie 1 to 8:
```
((Direct.L 1 Direct.^ Direct.L 2) Direct.^
 (Direct.L 3 Direct.^ Direct.L 4))
Direct.^
((Direct.L 5 Direct.^ Direct.L 6) Direct.^
 (Direct.L 7 Direct.^ Direct.L 8))
```
Doing a scan on this tree, `Direct` assume the additive monoid on the naturals, and
so `let open Direct in scan (iota 3)` produces
```
(((Direct.L 0 Direct.^ Direct.L 1) Direct.^
  (Direct.L 3 Direct.^ Direct.L 6))
 Direct.^
 ((Direct.L 10 Direct.^ Direct.L 15) Direct.^
  (Direct.L 21 Direct.^ Direct.L 28)))
, 36
```
The two most elegant implementations are in the modules `TopDown` and `BottomUp`,
which implement the 'pair of trees' and 'tree of pairs' approaches described by Elliot
in his talk. Once the two tree data types have been defined and supplied with functions
for mapping, zipping and unzipping, the two scan functions are remarkably similar. They
are both defined for general monoids and use implicit record arguments to mimic typeclasses
for functorial mapping, zipping and unzipping which can be applied to 'pairs' and 'trees'
uniformly. Here are the results of two scans:
```
> let open TopDown in let instance M = AddNat in scanT (iota 3)

TopDown.B
(TopDown.B
 (TopDown.B (TopDown.L 0 # TopDown.L 1) #
  TopDown.B (TopDown.L 3 # TopDown.L 6))
 #
 TopDown.B
 (TopDown.B (TopDown.L 10 # TopDown.L 15) #
  TopDown.B (TopDown.L 21 # TopDown.L 28)))
, 36
```
Each branch (`B`) is a pair (`_ # _`) of trees. Now using the 'bottom-up' tree, where,
in a tree of items of type A, a branch node is a tree of pairs, ie a tree of (A x A).
What this means in practise is that a binary tree of depth, say 3, which has 8 leaves, starts
with 3 levels of unary `B` constructors (ie not looking like a tree at all), and ends with a 
single `L` constructor containing a pair of pairs of pairs, so that the actual tree is 
represented entirely as nested pairs. Here is the result:
```
> let open TopDown in let instance M = AddNat in scanT (iota 3)

BottomUp.B
(BottomUp.B
 (BottomUp.B
  (BottomUp.L (((0 # 1) # (3 # 6)) # ((10 # 15) # (21 # 28))))))
, 36
```
What the bottom-up tree makes easy in comparison with the top-down tree is computations
on adjacent pairs of leaves, since each pair of leaves in the outer tree is a *single* leaf in
the nested tree of pairs. While the top-down tree makes it easy to work on the *top* N levels 
of the tree (eg by pattern matching), the bottom-up tree makes it easy to work on the *bottom*
N levels of the tree, by digging through N levels of `B` constructors and then applying a map.

What emerges from the Agda versions is that, when the type of container is an algberaic type
```math
    T a = a + F (G a)
``` 
where $F$ and $G$ are 'scannable' functors (one or both of which might involve $T$),
then, for monoidal types $a$ with 0 and + as the 'zero' and 'add' operations of the monoid
respectively, then $T$ is scannable with
```
    scan = scan <+> first (zipWith (map . (+)) . swap) . assocl . second scan . unzipWith scan
```
where `f <+> g` is a function that applies f or g to whichever side of a sum type is provided,
and `first` and `second` are as defined in Haskell's Arrow library, ie applying
a function to the first or second element of a pair.

The left-hand side of the `<+>` is just a scan over a leaf node, ie `scan x = (0, x)`.
To talk through the right hand side of the `<+>`, it says, to do a scan over F (G a), we scan each
of the sub-collections inside the outer `F` container and unzip the results to get two `F` containers
that are the same shape. The first contains `G` sub-containers  containing the results of the
many little scans (let's call them G-scans). The second contains the totals for each of those 
sub-scans. This is itself then scanned, this time using an F-scan, to get cumululative totals
at the coarser level implied by the outer F-container. Then we rearrange things to bring the two 
F-containers together: one containing many sub-scans and the other containing the cumuluative
coarse grained scan. Finally, we zip these together at the F-level, in each case using `map` to
add the coarse grained cumulative total to all the elements in each sub-scan.

Described in this way, it sounds intuitively correct no matter what the $F$ and $G$ functors
are (as long as they are scannable), and so would seem to generalise to containers built from 
many possible arrangements of functors, as long as each functor supports zip and unzip. 
In the case of the top down tree, we have the recursive type
```math
    T a = a + \mathit{Pair}\,(T a)
```
(where the left of the sum type is represented by a leaf node constructor `L` in the Agda code) 
and for the bottom up tree we have
```math
    T a = a + T (\mathit{Pair}\, a)
```
This is indeed what Conal goes on to do in his talk, considering how the scans for a number
of basic funtors can be composed to get the scan for a composition of functors.
and I will aim to do in this Agda version a some point in the future.


### Second try
In `scan2.agda` we have another go at this via a more compositional approach that
rests on defining how to scan some basic functorial building blocks:
- the $A \mapsto \mathit{Unit}$ functor, which only ever contains the value `Unit`
- the identity functor $A \mapsto A$, which just contains one value of a given type
- the product functor $A \mapsto F A \times G A$, ie a pair of containers given two
  functors $F$ and $G$.
- the composition functor $A \mapsto F (G A)$ for two functors $F$ and $G$.

Each of these functor combinators provides instances for `Zip` and `Scan` type classes
as well as `Functor`, so that we can build `scan` functions compositionally for types
built algebraically from these compoonents.
This seems to work well enough to allow us to generate scan functions for top down
trees, bottom up trees, and 'bushes' all in a very few lines towards the end of the module.

Note, there is an alternative branch called `more_tagged` that uses a new (tagged)
data type to represent the identity functor transformer. This seems to help Agda's
instance resolution algorithm so that not so many instance arguments need to be given
explicitly, at the cost of more layers of type constructors in the resulting data
structures.

### Todo in Agda version
- Try to get implicit instance resolution working better in scan2.agda.
- Try to understand the essence of 'zippable' and 'unzipable' functors. For example, any 
  functor can be unzipped via two maps, but what makes it possible to do this with one
  traversal? The answer is probably something to do with Haskell's Traversable type class..


## Ocaml version

Quite similar in spirit to the Agda version, but without the implicit arguments, so
that various versions are represented as functors parameterised by a MONOID module.
The examples use `Int` or `NoisyInt` as an additive monoid. `NoisyInt`
requires package `delimcc` (do `opam install delimcc`), in order to implement
couting of addition operations as an effect.

To build and then run in utop:
```bash
    dune build
    dune utop
```
then do `open Parscan`. Alternatively, to run without compiling, just run `utop`
- the `.ocamlinit` file will load the `delimcc` package and `scan.ml`.
Once in utop, you can run scans. For example, we can do a scan on a top-down tree
and get the number of additions performed like this:
```
utop # NoisyInt.counting_adds (fun () -> TopDownInt.(scan (iota 3)));;
- : (int TopDownInt.T.t * int) * int =
((TopDownInt.T.B
   (TopDownInt.T.B
     (TopDownInt.T.B (TopDownInt.T.L 0, TopDownInt.T.L 1),
      TopDownInt.T.B (TopDownInt.T.L 3, TopDownInt.T.L 6)),
    TopDownInt.T.B
     (TopDownInt.T.B (TopDownInt.T.L 10, TopDownInt.T.L 15),
      TopDownInt.T.B (TopDownInt.T.L 21, TopDownInt.T.L 28))),
  36),
 31)
```
where as with a bottom up tree, we get
```
utop # NoisyInt.counting_adds (fun () -> BottomUpInt.(scan (iota 3)));;
- : (int BottomUpInt.T.t * int) * int =
((BottomUpInt.T.B
   (BottomUpInt.T.B
     (BottomUpInt.T.B
       (BottomUpInt.T.L (((0, 1), (3, 6)), ((10, 15), (21, 28)))))),
  36),
 21)
```
Notice the smaller number of additions required. The difference becomes more marked
as we increase the size of the input:

```
utop # snd (NoisyInt.counting_adds (fun () -> TopDownInt.(scan (iota 8))));;
- : int = 2303

utop # snd (NoisyInt.counting_adds (fun () -> BottomUpInt.(scan (iota 8))));;
- : int = 765
```
The former is O(N log N) in the size of the input, while the latter is O(N).

### Depth constrained trees

In the bottom half of `scan.ml` there are some versions which use a phantom type parameter to
encode the depth of the tree in its type, to mimic the Agda version and provide more
precise types. The modules `BoundedTopDown` and `BoundedBottomUp` do this, as well as taking
the opportunity to replace the complicated `iota` function with a much simpler `const` function,
which fills a tree with a constant value in all the leaves. `iota` can then be implemented
simply by scanning a tree filled with 1s. Unfortunately, specifying the depth of a tree can
no longer be done with an `int`, but with a Piano encoded natural, eg `Zero`, `Suc Zero`, etc.
For example:
```
utop # BTopDownInt.(iota (Suc (Suc (Suc Zero))));;
- : (zero suc suc suc, int) BTopDownInt.S.T.t * int =
(BTopDownInt.S.T.B
  (BTopDownInt.S.T.B
    (BTopDownInt.S.T.B (BTopDownInt.S.T.L 0, BTopDownInt.S.T.L 1),
     BTopDownInt.S.T.B (BTopDownInt.S.T.L 2, BTopDownInt.S.T.L 3)),
   BTopDownInt.S.T.B
    (BTopDownInt.S.T.B (BTopDownInt.S.T.L 4, BTopDownInt.S.T.L 5),
     BTopDownInt.S.T.B (BTopDownInt.S.T.L 6, BTopDownInt.S.T.L 7))),
 31)
```
Here, 31 additions were required to scan over a top-down tree containing 8 1s.
Using the bottom-up version, we get
```
utop # BBottomUpInt.(iota (Suc (Suc (Suc Zero))));;
- : (zero suc suc suc, int) BBottomUpInt.T.t * int =
(BBottomUpInt.T.B
  (BBottomUpInt.T.B
    (BBottomUpInt.T.B (BBottomUpInt.T.L (((0, 1), (2, 3)), ((4, 5), (6, 7)))))),
 21)
```

## Haskell version

In the `haskell` subdirectory. This contains a few modules exploring similar constructs
as are found in the Agda version; indeed the Agda version served as a very useful guide
when navigating the complex landscape of Haskell type-level programming.

### module Common
The file `common.hs` contains the module `Common`, It provides some basic tools including
the type classes `Zippable` and `Scannable`, with instances for a `Pair` type, and functions
that implement fallback algorithms for `zipWith` and `unzipWith` relying only on `Applicative`
and `Functor` instances respectively. 

It also provides a scan function `scanTraversable` that
works for any `Traversable` instance, but is purely sequential and doesn't allow any parallelism.

Finally, there is some fun with type level naturals in order to support depth tagged tree
structures in the other modules.

In most cases, the easiest way to test if a particular data type supports the `scan` function
from the `Scannable` type class is to try `iota`, which (relying also the `Applicative` instance)
applies `scan` to a tree full of 1s in order to get an ascending sequence of integers starting
at 0.

### module Simple
Direct approach to top-down tree, using a `B` data constructor with two subtree arguments.
```haskell
ghci> :l simple.hs
ghci> iota :: T Three Int
B (B (B (L 0) (L 1)) (B (L 2) (L 3))) (B (B (L 4) (L 5)) (B (L 6) (L 7)))
```
### module TopDown
Another top-down tree, this time the `B` constructor takes a pair of subtrees. The `Applicative`
instance is defined for all depths in one go using some tricksy type level naturals, but
this seems to require some constraints to be added to GADT data constructors in a couple of places.
The basic structure of `scan` for a composition of two functors emerges here in the second
clause of `scan`, but referring directly to zip, unzip and scan functions for `Pair`.

### module TopDown2
Yet another top-down tree, this time deriving more instances automatically and deriving
`Applicative` inductively in two clauses, avoiding the type level natural shenanigens.
The `scan` function now handles the `Pair` functor implicity via its `Zippable`, `Functor`
and `Scannable` instances.

### module BottomUp
A bottom-up tree as a GADT. Once the `Zippable` instance is defined, the `scan` function
is identical to the version in `TopDown2`.
```haskell
ghci> :l bottomup.hs 
[1 of 2] Compiling Common           ( Common.hs, interpreted )
[2 of 2] Compiling BottomUp         ( bottomup.hs, interpreted )
Ok, two modules loaded.
ghci> iota :: T Three Int
B (B (B (L (((0 :# 1) :# (2 :# 3)) :# ((4 :# 5) :# (6 :# 7))))))
```

### module Algebraic
This is where things get interesting. We're trying to get at the idea that the scan
function is built up compositionally depending on the composition of functors used to
build a data structure. Several useful functor 'combinators' are already provided in the 
standard library, including `Identity`, `Product` and `Compose`. They already have `Functor`
and `Applicative` instances, so all we need to do is provide `Zippable` and `Scannable`
instances and we should be able to build arbitrary scannable data structures.

It turns out we don't even need to define any new 'tree' data types to get this to work -
it's enough to define some type families (ie type level functions) to build the desired
types inductively. We can even define the 'bush' data structure in 3 lines of code.
```haskell
ghci> :l algebraic

ghci> iota :: TD Two Int
Compose ((Compose ((Identity 0):#(Identity 1))):#(Compose ((Identity 2):#(Identity 3))))

ghci> iota :: BU Two Int
Compose (Compose (Identity ((0:#1):#(2:#3))))

ghci> iota :: Bush Two Int
Compose (Compose (   ((Compose ((0:#1):#(2:#3))) :# (Compose ((4:#5):#(6:#7))))
                  :# ((Compose ((8:#9):#(10:#11))) :#(Compose ((12:#13):#(14:#15))))))
```
The `GeneralT` type family tries to factor out the commonality between the top-down and 
bottom up trees by taking a 'functor transformer' (a type level functor-to-functor function)
whos job is the build the 'branch' functor given the functor representing a one-level smaller
tree. (Come to think of it, if we were to remove the depth parameters, this would be rather
like a fixed-point combinator for functors, with the functor transformer provide in 'open
recursive' style...). The top down tree can be recovered by using `Compose Pair` as the
functor transformer:
```haskell
ghci> iota :: GeneralT (Compose Pair) Two Int
Compose ((Compose ((Identity 0):#(Identity 1))):#(Compose ((Identity 2):#(Identity 3))))
```
The bottom up tree can be recovered with the aid of a `Flip` higher-kinded type (implemented
as a `newtype` rather than a type family because type families can't be partially applied in 
certain contexts). Luckily, all the necessary instances can be derived automatically, so, 
remarkably, we can write this and get a sensible answer:
```haskell
ghci> iota :: GeneralT (Flip Compose Pair) Two Int
Flip (Compose (Compose (Identity ((0:#1):#(2:#3)))))
```

### module DataFamily
Yet another version of the top-down tree, this time using data families. I'm not sure
there's any point to this. (Imports `Algebraic`).

### module AlgebraicGADT
This is an alternative implementation of the generalised tree idea in `Algebraic.GeneralT`, 
but this time using a GADT instead of a type family. Deriving the necessary instances turned
out to be quite complicated, but it worked in the end:
```haskell
ghci> iota :: FT (Compose Pair) Two Int
B (Compose (B (Compose (L 0:#L 1)):#B (Compose (L 2:#L 3))))
ghci> iota :: FT (Flip Compose Pair) Three Int
B (Compose B (Compose B (Compose L (((0:#1):#(2:#3)):#((4:#5):#(6:#7))))))
```
