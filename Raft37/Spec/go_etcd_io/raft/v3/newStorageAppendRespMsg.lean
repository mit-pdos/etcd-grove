/-
`newStorageAppendRespMsg(r, rd)` (`rawnode.go:266`), Lean-first (2026-10-16, stage R5 of the
raft v3.7 retarget; the old proof stepped through it inline in `RawNode.acceptReady`'s).
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvRawnode

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

/-- `newStorageAppendRespMsg(r, rd)` builds a fresh `&pb.Message{Type: MsgStorageAppendResp,
To: new(r.id), From: new(LocalAppendThread), Term: new(r.Term)}`, with `Index`/`LogTerm` set to
`r.raftLog.lastEntryID()` when the log has unstable entries (unset, read as `0`, otherwise), and
`Snapshot` set to `rd.Snapshot` when it is not empty -- here it is `nil` (the node layer's
scope). The result is the acknowledgement `appendAckM id t e` with no entries, snapshot, context
or responses, owned as `raft.Step` takes it (`msgIn ml □`, the shape `RawNode`'s pending queue
holds, `pendSt`). Stated on what it reads of the raft struct: `id`, `Term`, the `raftLog` field
and the log (`RawNode.acceptReady` holds the struct open, `ownRaftPhysReady`). -/
abbrev newStorageAppendRespMsg.spec : Prop :=
  ∀ (r : Loc) (id t : w64) (l : Loc) (ls : LogState) (rd : Ready),
  rd.Snapshot' = null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      r.[raft, go!"id"] ↦□ id ∗ r.[raft, go!"Term"] ↦ t ∗
      r.[raft, go!"raftLog"] ↦ l ∗ ownRaftLog l ls }}
    (App (App (Val #(functions newStorageAppendRespMsg [])) (Val #r)) (Val #rd))
  {{ (ml : Loc), RET #ml;
      msgIn ml DFrac.discard
        ⟨appendAckM id t (if ls.uents ≠ [] then plogLast ls.prev (ls.sents ++ ls.uents)
                          else entryID.mk (W64 0) (W64 0)), [], none, [], []⟩ ∗
      r.[raft, go!"Term"] ↦ t ∗ r.[raft, go!"raftLog"] ↦ l ∗ ownRaftLog l ls }}

end spec

end EtcdGrove
end Perennial
