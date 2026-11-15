/-
## `newStorageAppendRespMsg(r, rd)` (internal)

`acceptReady` (`rawnode.go:421`). Mirrors the code: a fresh `MsgStorageAppendResp` to the node from
the local append thread, at the node's term, with the log's last entry id if it has unstable entries
(R3's `lastEntryID`), and the `Ready`'s snapshot (shared, read-only). The entry id is what makes the
acknowledgement's `stableTo` sound (R3's `StableOk`). **Changes.** New; round 1: the entry id stated,
over the opened struct.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

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

/-- (internal) The storage-append acknowledgement of a batch. -/
def newStorageAppendRespMsg.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (rd : go_etcd_io.raft.v3.Ready) (os : Option Snapshot),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ snapOpt rd.Snapshot' os }}
    (App (App (Val (@! go_etcd_io.raft.v3.newStorageAppendRespMsg)) (Val #r)) (Val #rd))
  {{ (p : Loc), RET #p; ∃ mm, raftOpen r γ id o ∗ msgPts p (DFrac.own 1) mm ∗
      ⌜mm.type = MsgStorageAppendResp ∧ mm.to = id ∧ mm.src = localAppendThread ∧
        mm.term = o.view.hs.term ∧ mm.snapshot = os ∧
        (o.log.us.ents ≠ [] → uint.nat mm.index = o.log.lastIndex ∧
          o.log.termOf o.log.lastIndex = some mm.logTerm) ∧
        (o.log.us.ents = [] → mm.index = W64 0 ∧ mm.logTerm = W64 0)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
