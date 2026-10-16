/-
Proof of `Spec/go_etcd_io/raft/v3/needStorageAppendRespMsg.lean`. Lean-first (stage R5: the old
proof inlined it in `RawNode.acceptReady`'s).
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.needStorageAppendRespMsg
public import Raft37.Spec.go_etcd_io.raft.v3.raftLog__hasNextOrInProgressUnstableEnts
public import Raft37.Spec.go_etcd_io.raft.v3.IsEmptySnap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The log's unstable entries, then (when there are none) the `Ready`'s snapshot, `nil`. -/
theorem needStorageAppendRespMsg.wp_proof
    (wp_raftLog_hasNextOrInProgressUnstableEnts :
      raftLog.hasNextOrInProgressUnstableEnts.spec (GF := GF) (hG := hG))
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG)) :
    needStorageAppendRespMsg.spec (GF := GF) (hG := hG) := by
  intro r l ls rd Hsn
  wp_start as ⟨Hrl, Hlog⟩
  wp_auto
  wp_apply wp_raftLog_hasNextOrInProgressUnstableEnts $$ [$Hlog] as %b ⟨Hlog, %Hb⟩
  cases b
  · wp_auto
    wp_apply wp_IsEmptySnap rd.Snapshot' (DFrac.own 1) none $$ [] as %b' ⟨%Hb', -⟩
    · simp only [snapOpt]; ipureintro; exact Hsn
    simp only [Option.elim] at Hb'
    subst Hb'
    rw [← Hb]
    simp only [Bool.not_true]
    iapply HΦ
    iframe
  · wp_auto
    rw [← Hb]
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
