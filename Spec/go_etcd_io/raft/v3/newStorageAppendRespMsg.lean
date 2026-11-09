/-
## `newStorageAppendRespMsg(r, rd)` (internal)

`acceptReady`. Mirrors the code: a fresh `MsgStorageAppendResp` to the node from the local append
thread, at the node's term, with the log's last entry id if it has unstable entries (R3:
`lastEntryID`), and the `Ready`'s snapshot (shared, read-only). **Changes.** New (no old spec; the
old `acceptReady`'s proof inlined it). **Margin.** The entry id is not stated (`ackOk` carries it).
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

/-- (internal) The storage-append acknowledgement of a batch. -/
def newStorageAppendRespMsg.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (rd : go_etcd_io.raft.v3.Ready)
    (o : Option Snapshot),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ snapOpt rd.Snapshot' o }}
    (App (App (Val (@! go_etcd_io.raft.v3.newStorageAppendRespMsg)) (Val #r)) (Val #rd))
  {{ (p : Loc), RET #p; ∃ mm, raftCore r γ id ρ ∗ msgPts p (DFrac.own 1) mm ∗
      ⌜mm.type = MsgStorageAppendResp ∧ mm.to = id ∧ mm.src = localAppendThread ∧
        mm.term = ρ.hs.term ∧ mm.snapshot = o⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
