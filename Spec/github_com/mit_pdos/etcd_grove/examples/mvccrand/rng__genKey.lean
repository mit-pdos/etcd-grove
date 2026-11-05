/- Lean-first (no Rocq counterpart).

`r.genKey()` (`examples/mvccrand/mvccrand.go`): a fresh byte slice of one of the tester's keys
(`keyList`), the generator's state advanced.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- See the file header. -/
abbrev rng.genKey.spec : Prop :=
  ∀ (r : Loc) (g : rng),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      r ↦ g }}
    (App (Val (r @!! go.GoType.PointerType rng.ty @!! go!"genKey")) (Val #()))
  {{ (sl : GoSlice), RET #sl; (∃ g' : rng, r ↦ g') ∗
      ∃ k : GoString, sl ↦* k ∗ ownSliceCap w8 sl (DFrac.own 1) ∗ ⌜k ∈ keyList⌝ }}

end spec

end mvccrand
end EtcdGrove
end Perennial
