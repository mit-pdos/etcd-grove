/-
`sort.Reverse`: the trust boundary (Perennial translates `sort` without `Reverse` and the
`reverse` type's methods). Lean-first; see `Spec/sort/Sort.lean`.

`sort.Reverse(x)` returns `&reverse{x}` as a `sort.Interface`: its `Len` and `Swap` are `x`'s
(promoted), its `Less(i, j)` is `x.Less(j, i)`. So it sorts the same list with the order
flipped.
-/
module

public import Spec.sort.Sort

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `sort.Reverse(x)` of a sorter over `R` with order `lt`: a sorter over `R` with the order
flipped. -/
abbrev sort.Reverse.spec : Prop :=
  ∀ (E : Type) (x : GoInterfaceOk) (R : List E → IProp GF) (lt : E → E → Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ sorterSpec x R lt }}
    (App (Val (@! sort.Reverse)) (Val #(GoInterface.ok x)))
  {{ (y : GoInterfaceOk), RET #(GoInterface.ok y); sorterSpec y R (fun a b => lt b a) }}

end spec

end EtcdGrove
end Perennial
