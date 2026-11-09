/-
`(*store).Commit()` (`kvstore.go:286`).

**Users**: `KV.Commit` on the server's store (promoted): the snapshot paths (`server.go:2129`,
`snapshot_merge.go:36`: the backend's committed image, 2d's item 1); the tester (`mvccrand.go:599`).
Snippet `ReqCommit`.

**Proof sketch**: `s.mu.Lock()` (no transaction in flight), `s.b.ForceCommit()` (`keyBackend`:
`X ∗ storageReq B Pk X Y` to `Y`; `B` the store's by `mvccBackend`'s agreement), `s.mu.Unlock()`.

**Changes** from `specs-ref`'s `store__Commit.lean`: the contract at `*store`; no reader token (the
call takes `s.mu` exclusively and reads nothing).

**Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

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

/-- `KV.Commit`'s contract at `*store`. -/
def store.Commit.spec : Prop :=
  ∀ s : Loc, KV.Commit.contract (GF := GF) (go.GoType.PointerType store.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
