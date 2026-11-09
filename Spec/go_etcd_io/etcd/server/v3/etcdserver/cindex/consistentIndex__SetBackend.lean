/-
`(*consistentIndex).SetBackend(be)` (`cindex.go`): under the mutex, the backend replaced and the
index reset to `0` (the next `ConsistentIndex()` reads the new backend).

**Users**: `applySnapshot` (`server.go:1080`, the snapshot's backend, before the lessor and mvcc
recover from it), bootstrap (`bootstrap.go`, the opened backend: batch 2e). Snippet
`ReqReloadAfterSetBackend`.

**Proof sketch**: lock; store `be` and `SetConsistentIndex(0, 0)` (the store of the index is the
linearization point; `ciWriter`); unlock.

**Changes**: over `ciState` with the new backend's stored index `beStoredCI be v` (provisional, 4a's).
**Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.Api

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

/-- **Point the indexer at backend `be`** (whose stored index is `v`): index `0`, to be reloaded. -/
def consistentIndex.SetBackend.spec : Prop :=
  ∀ (l : Loc) (γ : CINames) (be : GoInterface) (v : w64) (Φ : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isCI l γ ∗ ciWriter γ ∗ beStoredCI be v ∗
      (AU <{ ∃∃ (m : CIState), ciState γ m }> @ ⊤, ∅
        <{ ciState γ { m with idx := W64 0, be := be, stored := some v }, COMM Φ }>) }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty @!!
      go!"SetBackend")) (Val #be))
  {{ RET #(); ciWriter γ ∗ Φ }}

end spec
end Cindex
end EtcdGrove
end Perennial
