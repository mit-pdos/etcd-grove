/-
`(*store).Restore(b)` (`kvstore.go:292`).

**Users**: `KV.Restore` on the server's watchable store (which wraps it, 3f): `applySnapshot`
(`server.go:1094`, after `lessor.Recover`, before the new backend's hook is set at `:1098`).
Snippet `ReqRestore` (`examples/specreq/mvcc/restore.go`).

**Proof sketch**: `s.mu.Lock()` (no transaction, so every reader slot of the old storage held through
a token is back in the store); `close(s.stopc)`, `s.fifoSched.Stop()` (the open token's: the pending
jobs run, a running compaction job interrupted, its resources back: `kbSafe B`, its slot); the new
storage and a fresh index; `currentRev := 1`, `compactMainRev := -1` under `s.revMu`; a new
scheduler and `stopc`; `restore()` over `B'` (as `NewStore`'s: the index rebuilt from the image of
`σ'.kv`, the leases attached, an unfinished compaction resumed with `B'`'s hook and commit
request); the caller's update fires when `currentRev` is set to `σ'.rev`. The old storage's rest
(`storageRest B`) back; `mvccBackend γ 1 B' Pk'`.

**Changes** from `specs-ref`'s `store__Restore.lean`: the contract at `*store` over the storage
contract (no backend or snapshot machinery), the lessor's writer token moved by the re-attachment (`RestoreLs`) in place of a premise
that every key's lease is live.

**Margin**: the metrics reporters are reset (not stated).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `KV.Restore`'s contract at `*store`. -/
def store.Restore.spec : Prop :=
  ∀ s : Loc, KV.Restore.contract (GF := GF) (go.GoType.PointerType store.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
