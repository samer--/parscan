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
$$
    T a = a + F (G a)
$$ 
where $F$ and/or $G$ are 'scannable' functors (one or both of which might involve $T$),
then, for monoidal types $a$ with 0 and + as the 'zero' and 'add' operations of the monoid
respectively, then $T$ is scannable with
```
    scan = scan <+> first (zipWith (map . (+)) . swap) . assocl . second scan . unzipWith scan
```
where `f <+> g` is a function that applies f or g to whichever side of a sum type is provided,
and `Monoid a ^ x : a => scan x = (0, x)`, ie the scan for a leaf value is just a pair of zero
and the value itself. `first` and `second` are as defined in Haskell's Arrow library, ie applying
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

Described in this way, this would seem to generalise to containers built from any arrangement of
functors, as long as each functor supports zip and unzip. This indeed what Conal goes on to
do in his talk and I will aim to do in this Agda version a some point in the future.

### Todo in Agda version
- The 'bash' tree as described in the talk.
- Parameterisation of scan over the sequence of functors used to build the tree.
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

[TBD]
