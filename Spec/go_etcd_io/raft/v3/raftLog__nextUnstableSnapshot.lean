/-
`raftLog.nextUnstableSnapshot` (`log.go:277`), Lean-first (D22 S-d3a, 2026-10-21).
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `l.nextUnstableSnapshot()` (`log.go:277`) is `l.unstable.nextSnapshot()`: `nil` exactly with no
snapshot pending or the pending one in progress; otherwise a fresh clone of the pending snapshot
(`proto.Clone`), owned by the caller, holding a record of the pending snapshot's id, a snapshot
the node may send (`ksn`), its index past `0` (`LogStoreOk`). `RawNode.readyWithoutAccept` hands
it out in `rd.Snapshot`. -/
abbrev raftLog.nextUnstableSnapshot.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"nextUnstableSnapshot")) (Val #()))
  {{ (p : Loc), RET #p; ownRaftLog l ls ∗ ⌜p = null ↔ (ls.snap = none ∨ ls.sip = true)⌝ ∗
      (⌜p = null⌝ ∨ ∃ (sid : entryID) (sv : SnapshotM),
        ⌜ls.snap = some sid ∧ ls.sip = false ∧ snapId sv = sid ∧
          snapTrip sv sv.Metadata'.ConfState'.lists ∈ ls.ksn ∧ 0 < uint.Z sid.index'⌝ ∗
        ownSnapM p (DFrac.own 1) sv) }}

end spec

end EtcdGrove
end Perennial
