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
type constructor `C` is, in Haskell-ish notation 
```
    Monoid A => C A -> (C A, A)
```
The talk looks at how the idea of scanning can be generalised from the familiar 
(sequential) algorithm for scanning a list to more parallelisable structures for
containter types built from different combinations of functors.
    
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
`let open Direct in scan (iota 4)` results in
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
The two most suggestive implementations are in the modules `TopDown` and `BottomUp`,
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
single `L` constructor containing a pair of pair of pairs, so that the actual tree is 
represented entirely as nested pairs. here is the result of a scan:
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
the nested tree of pairs.

What emerges from the Agda versions is that, if the type of container is an algberaic type
```
    T a = a + F (G a)
``` 
where `F` and/or `G` are 'scannable' functors (one or both of which might involve T),
then, for monoidal types `a` with 0 and (+) as the 'zero' and 'add' operations of the monoid,
then `T` is scannable with
```
    scan = scan <+> first (zipWith (map . (+)) . swap) . assocl . second scan . unzipWith scan
```
where f <+> g` is a function that applies f or g to whichever side of a sum type is provided,
and `Monoid a ^ x : a => scan x = (0, x)`, ie the scan for a leaf value is just a pair of zero
and the value itself. `first` and `second` are as defined in Haskell's Arrow library, ie applying
a function to the first or second element of a pair.

To talk through the right hand side of the `<+>`, it says, to do a scan over F (G a), we scan each
of the sub-collections inside the outer `F` container and unzip the results to get two `F` containers
that are the same shape. The first contains `G` sub-containers  containing the results of the
many little scans (which are all G-scans). The seconds contains the total sum for each of those 
sub-scans - this is itself then scanned, this time using an F-scan, to get cumululative totals
at the coarser level implied by the outer F-container. Then we rearrange things to bring the two 
F-containers together: one containing many sub-scans and the other containing the cumuluative
coarse grained scan. Finally, we zip these together at the F-level, in each casing using map to
add the coarse grained cumulative total to all the elements in each sub-scan.

Described in this way, this would *seem* to generalise to containers built from any arrangement of
functors, as long as each functor supports zip and unzip.

### Todo in Agda version
- The 'bash' tree as described in the talk.
- Parameterisation of scan over the sequence of functors used to build the tree.
- Try to understand the essence of 'zippable' and 'unzipable' functors. For example, any 
  functor can be unzipped via two maps, but what makes it possible to do this with one
  traversal? The answer is probably something to do with Haskell's Traversable type class..


## Ocaml version

Requires package `delimcc` (do `opam install delimcc`), but this is only
needed for the tooling that counts additions performed when doing a scan.

To build and then run in utop:
```bash
    dune build
    dune utop
```
Or to run without compiling, just run `utop` - the `.ocamlinit` file will
load the `delimcc` package and `scan.ml`.

## Haskell version

[TBD]
