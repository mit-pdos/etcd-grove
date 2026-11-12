/-
`(*consistentIndex).UnsafeSave(tx)` (`cindex.go`): loads the index and term and writes them into
the write transaction (`schema.UnsafeUpdateConsistentIndex`: nothing for index `0`; with
`ETCD_VERIFY` on, a panic if the index decreases).

**Users**: the backend's pre-commit hook (`storage/hooks.go:46`, `BackendHooks.OnPreCommitUnsafe`,
batch 2e), run by the backend's commit goroutine under the batch transaction's lock, concurrently
with the apply thread: a reader, no writer's token. Snippet `ReqSaveInCommit`.

**Proof sketch**: the load of `consistentIndex` is the linearization point (the client's update sees
the state and must know the index does not decrease against the transaction's stored one: the
server's batch-lock invariant, the index only grows while the backend is the same); the term's load
is any value; 4b's `UnsafeUpdateConsistentIndex` over `txStoredCI` (provisional) writes `v` unless
it is `0`.

**Changes**: logically atomic over `ciState` (was the owned index). **Margin**: the stored term is
not modelled (a mixed pair is possible: the setter stores the index first).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cindex

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

/-- **Save the index into a commit**: the transaction's stored index becomes the in-memory one at
the load (unchanged if that is `0`). -/
def consistentIndex.UnsafeSave.spec : Prop :=
  ∀ (l : Loc) (γ : CINames) (tx : GoInterface) (c : w64) (Φ : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isCI l γ ∗ txStoredCI tx c ∗
      (AU <{ ∃∃ (m : CIState), ciState γ m ∗ ⌜m.idx = W64 0 ∨ uint.nat c ≤ uint.nat m.idx⌝ }>
          @ ⊤, ∅
        <{ ciState γ m, COMM Φ m.idx }>) }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty @!!
      go!"UnsafeSave")) (Val #tx))
  {{ RET #(); ∃ v, Φ v ∗ txStoredCI tx (if v = W64 0 then c else v) }}

end spec
end Cindex
end EtcdGrove
end Perennial
