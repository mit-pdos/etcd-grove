/-
Port of `election_proof/proof_raftLog__entries.v`.
-/
import EtcdGrove.Raft.Spec.raftLog__entries
import EtcdGrove.Raft.Spec.raftLog__lastIndex
import EtcdGrove.Raft.Spec.raftLog__slice

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftLog.entries.wp_proof
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_slice : raftLog.slice.spec (GF := GF) (hG := hG)) :
    raftLog.entries.spec (GF := GF) (hG := hG) := by
  intro l ls i maxSize Hlo
  wp_start as Hlog
  iNamed Hlog
  wp_auto
  icases ownRaftLog_nowrap l ls $$ Hlog with ⟨%Hnw, Hlog⟩
  wp_apply wp_raftLog_lastIndex l ls $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
  wp_if_destruct
  · -- `i` is past the end: `nil` and no error; the log is untouched.
    iapply HΦ
    iframe Hlog
    isplitl
    · iapply ownSlice_nil (V := raftpb.Entry)
    · ipureintro
      exact ⟨fun e He => absurd He (List.not_mem_nil), List.nil_prefix⟩
  · wp_apply wp_raftLog_lastIndex l ls $$ [$Hlog] as %li2 ⟨Hlog, %Hli2⟩
    wp_apply wp_raftLog_slice l ls _ _ _ (by word) $$ [$Hlog] as %sl %es ⟨Hlog, Hsl, %Hes, -⟩
    obtain ⟨-, -, Hin, Hpre⟩ := Hes
    iapply HΦ
    iframe Hlog Hsl
    ipureintro
    exact ⟨Hin, Hpre⟩

end proof

end EtcdGrove
end Perennial
