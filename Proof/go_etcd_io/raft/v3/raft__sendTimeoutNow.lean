/- Lean-first (no Rocq counterpart), 2026-10-13. -/
module

public import Spec.go_etcd_io.raft.v3.raft__sendTimeoutNow
public import Spec.go_etcd_io.raft.v3.raft__send

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

/-- `send`'s clause for an undescribed type: `Term = 0`, not to oneself, nothing queued
abstractly. -/
theorem raft.sendTimeoutNow.wp_proof
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG)) :
    raft.sendTimeoutNow.spec (GF := GF) (hG := hG) := by
  intro cfg r id s to Hto
  wp_start as Hphys
  wp_auto
  let tn : raftpb.Message :=
    { Type' := W32 14, To' := to, From' := 0, Term' := 0, LogTerm' := 0, Index' := 0,
      Entries' := slice.nil, Commit' := 0, Vote' := 0, Snapshot' := null, Reject' := false,
      RejectHint' := 0, Context' := slice.nil, Responses' := slice.nil }
  have Hok : SendOk id s tn [] [] [] :=
    Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, rfl, Hto, rfl⟩)))
  wp_apply wp_raft_send cfg r id s tn [] [] [] (Or.inl rfl) Hok $$ [$Hphys] as Hphys
  · isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSlice_nil
    · iapply send_no_snap
      exact (by decide : W32 14 ≠ W32 7)
  ihave Hphys := ownRaftPhys_unsend cfg r id s $$ Hphys
  iapply HΦ
  iexact Hphys

end proof

end EtcdGrove
end Perennial
