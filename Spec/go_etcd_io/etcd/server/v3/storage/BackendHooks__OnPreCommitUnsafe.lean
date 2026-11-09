/-
## `(*BackendHooks).OnPreCommitUnsafe(tx)` (`hooks.go:43-52`): translated

**Users.** The backend's commit (4a: `batchTxBuffered.commit` calls its hooks under the batch
lock), through `backend.Hooks`.

**Proof sketch.** `indexer.UnsafeSave(tx)` (2d's `cindex`: the consistent index and term written to
the meta bucket), then under the hooks' lock the pending configuration, if any, written
(`schema.MustUnsafeSaveConfStateToBackend`, 4b) and cleared. Both writes go to the locked batch
transaction `tx` (`beTx`, 4a's, provisional); what they mean for the backend's image (the meta
keys at the applied index and configuration) is 2d's apply invariant.

**Changes** (from `specs-ref`'s `BackendHooks__OnPreCommitUnsafe.lean`): over provisional
predicates. **Margin.** The image's meaning is not stated here.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.Api
public import Spec.go_etcd_io.raft.v3.Api
public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ServerStorage

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **Writes the consistent index and the pending configuration** into the transaction. -/
def BackendHooks.OnPreCommitUnsafe.spec : Prop :=
  ∀ (h : Loc) (ci tx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ isHooks h ci ∗ beTx tx }}
    (App (Val (h @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendHooks.ty @!! go!"OnPreCommitUnsafe")) (Val #tx))
  {{ RET #(); beTx tx }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
