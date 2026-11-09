/-
`(*EtcdServer).createMergedSnapshotMessage(m, snapt, snapi, confState)` (`snapshot_merge.go:31-54`):
commit the KV, take a backend snapshot, stream it through a pipe, and replace `m`'s snapshot by one
at the applied index and term with the thread's `ConfState` (a copy) and no data.

**Users**: `applyAll` (`server.go:1013`), for a `MsgSnap` the node sent at the current raft term
whose snapshot is at or below the applied index. Snippet `snapshot.go` (`ReqMergedSnapshot`).

**Proof sketch**. The `ConfState` passed is the thread's (`ep.confState`: a configuration at a
committed point at or past the applied index, the replay's included; R1's `confStatePts`/`confAt`,
which `applyAll` reads off the thread). `s.KV().Commit()` (3e's: the backend's committed state is the state machine at
`c = max appliedi ci`, the hook saving `c`); `s.be.Snapshot()` (4a's: `beSnap bs γ c`);
`newSnapshotReaderCloser.spec` (the goroutine's thread token: `threadTok`); the new snapshot
`sn' = (snapi, snapt, cs, [])` is valid (R1's `snap_make`, as `snapshot.spec`: the delivered prefix
of length `snapi`, the configuration at `c ≥ snapi`), with its point (`snapPoint γ sn' c`) and its image (`imgAt γ snapi`, the backend at `c ≥ snapi`:
what the receiver's `dbIn` records); R1's `msgSent_replaceSnap` (premises: `m` a `MsgSnap` this node sent, its snapshot's
index at most `snapi`, `snapi` within the delivered log (`deliveredLb`, the thread's), `snapt ≤
m.term`: `issues/etcd-merged-snapshot-stale-term.md`) gives `msgSent` of the new message;
`snap.NewMessage(m, rc, dbsnap.Size())` (2e's snap package: a message whose reader is `rc`, its size
in `[0, 2^62)`, 4a's `Size`) gives `mergedSnap`.

**Changes** from `specs-ref`'s spec (the backend's data model `D`, `srvBeAddr`, `RS'`): over
`applyThread`/`mergedSnap`; the snapshot's index is any applied index (no window premise: the old
`winNoMergedSend` was false at restarts); the term guard is a premise (`snapt ≤ m.term`).

**Margin**: none.
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

/-- **Merge a `MsgSnap`** with the applied state: the message, its snapshot now at the applied index
and term with the thread's configuration, carrying the backend's image. -/
def EtcdServer.createMergedSnapshotMessage.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (ep mp cs : Loc) (p : Progress) (m : Raft.Msg)
    (sn : Raft.Snapshot) (csm : Raft.ConfState) (a : Nat) (mb : Raft.Membership),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ applyThread s γ ep p ∗ threadTok ∗
      Raft.confStatePts cs DFrac.discard csm ∗ Raft.confAt γ.raft a mb ∗
      ⌜csm.Is mb ∧ uint.nat p.appliedi ≤ a⌝ ∗
      Raft.msgPts mp (DFrac.own 1) m ∗ Raft.msgSent γ.raft m ∗
      ⌜m.type = Raft.MsgSnap ∧ m.src = W64 id ∧ m.snapshot = some sn ∧
        uint.nat sn.index ≤ uint.nat p.appliedi ∧ uint.nat p.appliedt ≤ uint.nat m.term⌝ }}
    (App (App (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"createMergedSnapshotMessage")) (Val #mp)) (Val #p.appliedt)) (Val #p.appliedi)) (Val #cs))
  {{ (mg : Loc), RET #mg; applyThread s γ ep p ∗
      mergedSnap mg γ { m with snapshot := some ⟨p.appliedi, p.appliedt, csm, []⟩ } }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
