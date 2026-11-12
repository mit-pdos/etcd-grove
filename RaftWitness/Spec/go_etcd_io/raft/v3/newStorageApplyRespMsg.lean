/-
`newStorageApplyRespMsg(r, ents)` (`rawnode.go:387`), Lean-first (2026-10-16, stage R5 of the
raft v3.7 retarget; the old proof stepped through it inline in `RawNode.acceptReady`'s).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `newStorageApplyRespMsg(r, ents)` builds a fresh `&pb.Message{Type: MsgStorageApplyResp,
To: new(r.id), From: new(LocalApplyThread), Term: new(uint64(0)), Entries: ents}`: the
acknowledgement `applyAckM id` whose `Entries` is the slice `ents` itself (shared, read-only:
`entsRO ents ce`, the committed entries a `Ready` handed out), owned as `raft.Step` takes it
(`msgIn ml □`, the shape `RawNode`'s pending queue holds, `pendSt`; no `Entries` capacity, which
`msgIn` asks only of a `MsgApp`). Stated on what it reads of the raft struct, `id`. -/
abbrev newStorageApplyRespMsg.spec : Prop :=
  ∀ (r : Loc) (id : w64) (ents : GoSlice) (ce : List EntryM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      r.[raft, go!"id"] ↦□ id ∗ entsRO ents ce }}
    (App (App (Val #(functions newStorageApplyRespMsg [])) (Val #r)) (Val #ents))
  {{ (ml : Loc), RET #ml; msgIn ml DFrac.discard ⟨applyAckM id, ce, none, [], []⟩ }}

end spec

end EtcdGrove
end Perennial
