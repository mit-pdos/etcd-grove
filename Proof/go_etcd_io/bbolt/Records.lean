/-
Keeping a record a variable: a typed points-to of a record term gives one of a fresh variable
equal to it (`typedPointsto_name`). A chain of `{ v with f := x }` updates (a struct written
field by field) otherwise builds a term whose size doubles with each field.
-/
module

public import Perennial.Golang.Theory.Pre

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode

theorem typedPointsto_name [FfiSyntax] {GF : BundledGFunctors} {V : Type}
    [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (dq : DFrac) :
    typedPointsto (GF := GF) l v dq ⊢ ∃ v', ⌜v' = v⌝ ∗ typedPointsto l v' dq := by
  iintro H
  iexists v
  isplitr
  · ipureintro; rfl
  · iexact H

end bbolt
end EtcdGrove
end Perennial
