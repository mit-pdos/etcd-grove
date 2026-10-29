/-
`isWellFormed(s)` (`resourceversion.go`): **the trust boundary** (gap C1: Goose does not translate
its `for i := range s`, so it is names only). The loop ranges over the rune start indices of `s`
and tests the byte there; a non-ASCII rune's first byte is not a digit, so it returns what the
byte loop would: `true` iff `s` is non-empty, has no leading `0` and is all ASCII digits
(`wellFormed`). Lean-first.
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.resourceversion.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace resourceversion

open Iris Iris.BI k8s_io.apimachinery.pkg.util.resourceversion

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.resourceversion.Assumptions]

/-- `isWellFormed(s)`: `wellFormed s` (a non-empty digit string with no leading `0`). -/
abbrev isWellFormed.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.resourceversion }}
    (App (Val (@! isWellFormed)) (Val #s))
  {{ RET #(wellFormed s); True }}

end spec

end resourceversion
end EtcdGrove
end Perennial
