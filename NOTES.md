# Notes

Turns out the Template Haskell now supports typed splices! Which is very
convenient for what I want to do.

```haskell
[|True|] :: Q Exp
[||True||] :: Code Q Bool
```
