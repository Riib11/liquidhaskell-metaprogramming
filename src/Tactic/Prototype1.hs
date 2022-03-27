module Tactic.Prototype1 where

{-
In LH, a goal is simply a boolean expression `goal`. So, whenever a tactic want's to check that the goal has been satisfied, it can just condition on `goal` i.e.

```
... if goal then trivial else ...
```

can appear anywhere in the tactic to check for success. However, the tactic (metaprogram) can't actually statically condition on this, so I have to handle two types of non-termination:
- the tactic doesn' terminate if it it has some sort of loop that repeatedly checks the goal
- the resulting liquidhaskell program doesn't pass termination checking if the program resulting from the tactic has loops

A potential solution is to make the tactic's loops use gas, so that they must terminate. What does this look like?

```
... \k nexts x gas -> if goal then trivial else  k next  (gas - 1)
```
This is implemented as Core.Loop
-}

import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax

-- reifyDatatype
