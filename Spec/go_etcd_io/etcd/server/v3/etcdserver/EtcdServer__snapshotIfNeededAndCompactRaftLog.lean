/-
`(*EtcdServer).snapshotIfNeededAndCompactRaftLog(ep)` (`server.go:1240-1249`): if a disk or memory
snapshot is due, take it and compact the raft log below it.

**Users**: `applyAll` (`server.go:1002`), after raft advanced past the batch. Snippet `snapshot.go`
(`ReqSnapshotCompact`).

**Proof sketch**. `shouldSnapshotToDisk.spec`, `shouldSnapshotToMemory.spec`; if either:
`snapshot.spec` (with `nodeAdvanced r appliedi`; `0 < appliedi` since a due snapshot is past an
earlier one or the snapshot count: `appliedi > memSnap + memorySnapshotCount` or
`appliedi - diskSnap > SnapshotCount` or, forced, `appliedi ≠ diskSnap`), giving `nodeSnapLb r
appliedi`; `compactRaftLog.spec` at `appliedi`.

**Changes** from `specs-ref`'s spec (the memory storage's ghost, the frozen ranges and terms
`srvFrozenRange`/`srvFrozenTerms`, `srvSnapState`): over `applyThread` with R1's facts as
`nodeAdvanced`/`nodeSnapLb`. **Margin**: the snapshot indices move; the post says only that the
applied index and term do not.
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

def EtcdServer.snapshotIfNeededAndCompactRaftLog.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : w64) (ep : Loc) (p : Progress),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ applyThread s γ ep p ∗
      nodeAdvanced (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s)
        (uint.nat p.appliedi) }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"snapshotIfNeededAndCompactRaftLog")) (Val #ep))
  {{ RET #(); ∃ p', applyThread s γ ep p' ∗
      ⌜p'.appliedi = p.appliedi ∧ p'.appliedt = p.appliedt⌝ }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
