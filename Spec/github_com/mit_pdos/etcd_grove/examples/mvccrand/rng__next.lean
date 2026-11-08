/- Lean-first (no Rocq counterpart).

`r.next()` (`examples/mvccrand/mvccrand.go`, a splitmix64 step): returns some number, the
generator's state advanced. The tester's checks hold whatever the generator returns, so the spec
says nothing of the value.
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
abbrev rng.next.spec : Prop :=
  ∀ (r : Loc) (g : rng),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      r ↦ g }}
    (App (Val (r @!! go.GoType.PointerType rng.ty @!! go!"next")) (Val #()))
  {{ (z : w64), RET #z; ∃ g' : rng, r ↦ g' }}

end spec

end mvccrand
end EtcdGrove
end Perennial
