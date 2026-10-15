/- Lean-first (no Rocq counterpart; 2026-10-12, read-index).

The commit index is within the log (`ownRaftLog_committed`), so `term` answers it
(`err = nil`) and `zeroTermOnOutOfBounds` passes its term through; the comparison with
`r.Term` (`s.term`) is then the spec's. (The spec's premise `s.term ≠ 0` is not needed.)
-/
module

public import Spec.go_etcd_io.raft.v3.raft__committedEntryInCurrentTerm
public import Spec.go_etcd_io.raft.v3.raftLog__term
public import Spec.go_etcd_io.raft.v3.raftLog__zeroTermOnOutOfBounds

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

theorem raft.committedEntryInCurrentTerm.wp_proof
    (wp_raftLog_term : raftLog.term.spec (GF := GF) (hG := hG))
    (wp_raftLog_zeroTermOnOutOfBounds :
      raftLog.zeroTermOnOutOfBounds.spec (GF := GF) (hG := hG)) :
    raft.committedEntryInCurrentTerm.spec (GF := GF) (hG := hG) := by
  intro c r id s _Hterm
  wp_start as Hpre
  iNamed Hpre
  wp_auto
  -- `r.raftLog.committed`, within the log
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hcb, Hlog⟩
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  wp_auto
  ihave Hlog := Hlb $$ Hl
  obtain ⟨Hcm, -⟩ := Hlv
  rw [Hcm]
  ihave Hphys := Hlogback $$ Hlog
  -- `term(committed)`: in bounds, so no error
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
  wp_apply wp_raftLog_term $$ [$Hlog] as %t %err ⟨Hlog, %Herr_iff, %Hterm_at, #Herr⟩
  ihave Hphys := Hlogback $$ Hlog
  have Herr : err = interface.nil := Herr_iff.2 ⟨Hcb.1.1, Hcb.1.2.2⟩
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  wp_apply wp_raftLog_zeroTermOnOutOfBounds $$ [$Herr] as %t' %Ht'
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  iapply HΦ
  iframe Hphys
  ipureintro
  rw [Ht' Herr, Hterm_at Herr]
  simp
