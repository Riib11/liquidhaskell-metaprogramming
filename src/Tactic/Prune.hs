module Tactic.Prune where

{-
GOAL:

Remove bad normals:

For each use of the `auto` tactic, check each normal in isolation for LH errors.
Only keep the normals that do not have LH errors.
I.e. discard the normals with LH errors.

Pruning unused normals:

For each use of the `auto` tactic, does binary search to find
the smallest subset of generated normals that still pass TH check.
I.e. discard the unused normals.
-}

{-
PROCESS:
- get TH spliced output
- make copy of input file with TH spliced output in designated location
- prune bad normals (at each `auto` site):
  - replace `auto` site with `undefined`
  - loop:
    - replaces `auto` site with the next normal combined with `undefined`
      (in a way that the undefined is not available in the refinement of the use)
    - run LH check
      - if passes LH check, then mark normal as _good_
      - if fails LH check, then mark normal as _bad_
  - only keep the _good_ normals
- prune unused normals (at each `auto` site):
  - loop1
    - select entire `auto` site as current site
      - prune 1/2 subset of normals in current site
      - loop2
        - run LH check
          - if passes, then loop1
          - if fails, then select next 1/2 subset of normals, then loop2
-}