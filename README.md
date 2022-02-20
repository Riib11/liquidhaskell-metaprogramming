# liquidhaskell-metaprogramming

LiquidHaskell is a plugin for Haskell that introduces decidable refinement types
(liquid types) to Haskell's type system. The user writes refinement type
specifications and LiquidHaskell's typechecker will use an SMT solver (e.g. Z3)
to check that that the user's implementations in fact satisfy those
specifications.

Refinement types are a subsystem of dependent type theory, where each refinement
type has the form

```
{x:a | p}
```

where `a` is a Haskell type and `p` is a boolean expression that can refer to
any variables in scope (including x). Theses are often called "subset types" in
dependent type theory, since it can be read as "the subset of `a` that satisfies
`p`". For example

```
x:{Int | 0 <= x} -> y:{Int | x < y} -> z:{Int | x <= z && z < y}
```

is the refinement type of a function that takes takes two integers and outputs
an integer between them.

## Lack of Explicit Refinement Types

Although Haskell has implicit polymorphism, it is possible to make the
polymorphism explicit using the `ExplicitForAll` and `TypeApplication` language
extensions:

```
-- implicit
id :: a -> a
id x = x

-- explicit type quantification
id :: forall a. a -> a
id x = x

-- explicit type application
test :: Int -> Int
test = id @Int
```

The same cannot exactly be said for refinement types. Since LiquidHaskell builds
strictlly on top of Haskell, it is impossible to reference refinement types in
normal Haskell code. There are a few practical consequences of this:

- no implicit parameters
- no branching conditional on refinements

### Consequence: No Implicit Parameters

<!-- TODO: come up with another equivalence relation example -->
<!-- https://math.stackexchange.com/a/2790998 -->

In most languages that support dependent type theory, term arguments can often
be inferred in the same way that Haskell infers type arguments for the sake of
implicit polymorphism. In Agda for example:

```
commutativity : forall m n -> m + n = n + m
commutativity m n = ...

1+2=2+1 : 1 + 2 = 2 + 1
1+2=2+1 = commutativity _ _
```

Just from the type that `commutativity _ _` is expected to have, its arguments
can be inferred and so can just be given as underscores (which mean "infer this
if possible, otherwise throw a type error").

This is not generally possible in LiquidHaskell because refinement types are
more amorphous. A term does not have a unique refinement type, since it also has
any refinement type that is implied by the refinement type it originally started
out with. Additionally, as more refinements come into context, those must be
accounted for as well in it's refinement type. For example

```
x:{Int | 0 <= x} -> y:{Int | x <= y} -> ...
```

Before `y` comes into scope, the refinement of `x` is just `0 <= x`, but as soon
as `y` comes into scope that refinement now contains `x <= y` as well. This
would all have to be handled manually if it were using strict subset types in
dependent type theory, but LiquidHaskell avoids this hassle by relying on an SMT
solver to put all the refinement together and figure out if they're satisfied.

This lacking leads to a lot of redundancy in LiquidHaskell code where
should-have-been implicit arguments have to be given many times. For example:

```
r :: a -> a -> Bool
r x y = ...

transitivity :: x:a -> y:{a | r x y} -> z:{a | r y z} -> z:{a | r x z}
transitivity x y z = ...

chain :: {r x v}
chain =
  transitivity x (y `by` ...)
    (transitivity y (z `by` ...)
      (transitivity z (w `by` ...) (v `by` ...)))
```

Here, we need to repeat `y` and `z` twice each.

Macros can be used to splice the same expressions into multiple places when
needed.

### Consequence: No Branching Conditional on Refinements

### Consequence: No Expansion of Unrefined Functions

Since refinement types only exist at the type level, any refinement-relevant
information of a term is only accessibly nonlocally if it is included in the
type.

Macros can be used to slice a template into an expression to take advantage of
local refinement-relevant information without the hastle of providing the whole
context to a function call.
