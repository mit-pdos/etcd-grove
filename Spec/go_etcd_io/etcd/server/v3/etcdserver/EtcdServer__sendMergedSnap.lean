/-
`(*EtcdServer).sendMergedSnap(merged)` (`server.go:1874-1914`): count the snapshot in flight (which
pauses the raft log's compaction), hand it to the transport, and attach a goroutine that releases the
count when the transport reports it sent (30 s later on success) or the server stops.

**Users**: `applyAll` (`server.go:1014`). Snippet `snapshot.go` (`ReqMergedSnapshot`).

**Proof sketch**: `inflightSnapshots.Add(1)` (an atomic: no invariant needed; `compactRaftLog` reads
it only to skip work); `s.r.transport.SendSnapshot(merged)` (2f's: takes `mergedSnap`, delivers the
message with its `msgSent` and the db reader's image to the peer's snapshot handler, which saves it
for `applySnapshot`'s `OpenSnapshotBackend`, `req/` 2f); `s.GoAttach(...)` (2e's: a goroutine of the
server's wait group) receiving from `merged.CloseNotify()` (2e's `snap.Message`) or `s.stopping`.

**Changes** from `specs-ref`'s spec: over `mergedSnap`. **Margin**: none.

Changes: verify-round (A7-provability F1, completeness F1): takes and gives back the thread's `threadTok`; `isServer s γ.etcd` (for `GoAttach`, `LeaseRevoke`, `raftRequest`) from `srvStarted_isServer`; each attached goroutine runs with its own fresh token (`GoAttach.spec`); the internal requests hold no `srvGate` share (`LeaseRevoke.spec` takes none; `raftRequest` never did).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

def EtcdServer.sendMergedSnap.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (mg : Loc) (m : Raft.Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id ∗ mergedSnap mg γ m ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"sendMergedSnap")) (Val #mg))
  {{ RET #(); threadTok }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
