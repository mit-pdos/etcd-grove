/-
## `lockedRand.Intn(n)` (internal)

`resetRandomizedElectionTimeout` (on the package's `globalRand`). **Proof sketch.** Under its mutex
(its lock invariant in the package's initialization); `crypto/rand.Int` on `big.NewInt(n)`
(Perennial's model: a value in `[0, n)`; its error is ignored by the code, so the spec rests on the
model's `rand.Reader` never failing, as Go's documents since 1.24). **Changes** (from `specs-ref`'s
`lockedRand__Intn.lean`): unchanged. **Margin.** None.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) A random number in `[0, n)`. -/
def lockedRand.Intn.spec : Prop :=
  ∀ (lr : Loc) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ typedPointsto (globalAddr go_etcd_io.raft.v3.globalRand) lr DFrac.discard ∗
      ⌜0 < sint.Z n⌝ }}
    (App (Val (lr @!! go.GoType.PointerType go_etcd_io.raft.v3.lockedRand.ty @!! go!"Intn")) (Val #n))
  {{ (v : w64), RET #v; ⌜0 ≤ sint.Z v ∧ sint.Z v < sint.Z n⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
