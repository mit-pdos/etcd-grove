/- Lean-first (no Rocq counterpart).

`r.intn(n)` (`examples/mvccrand/mvccrand.go`), for `n > 0`: some number in `[0, n)`, the
generator's state advanced.
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
abbrev rng.intn.spec : Prop :=
  ∀ (r : Loc) (g : rng) (n : w64), 0 < sint.Z n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      r ↦ g }}
    (App (Val (r @!! go.GoType.PointerType rng.ty @!! go!"intn")) (Val #n))
  {{ (x : w64), RET #x; (∃ g' : rng, r ↦ g') ∗ ⌜0 ≤ sint.Z x ∧ sint.Z x < sint.Z n⌝ }}

end spec

end mvccrand
end EtcdGrove
end Perennial
