/-
Port of `election_proof/proof_raftLog__lastEntryID.v`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftLog__lastEntryID
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftLog__term

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit [GooseInterp] [GooseSemantics] [GoGlobalContext] in
/-- Rocq `plog_last_eq`: on a well-formed log, the id read off `lastIndex()` and the
term there is `plogLast`. -/
private theorem plogLast_eq (b : entryID) (es : List EntryM) (t li : w64)
    (Hwf : PlogWf b es) (Hli : uint.Z li = plogLastIndexZ b es)
    (Ht : plogTermAt b es li = some t) :
    entryID.mk t li = plogLast b es := by
  have Hidx := plogLast_index b es Hwf
  have Hi : li = (plogLast b es).index' := by
    apply BitVec.eq_of_toNat_eq; simp only [uint.Z] at Hli Hidx; omega
  have Htl := plogTermAt_last b es Hwf
  rw [← Hi, Ht] at Htl
  cases Htl
  rw [Hi]

theorem raftLog.lastEntryID.wp_proof
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_term : raftLog.term.spec (GF := GF) (hG := hG)) :
    raftLog.lastEntryID.spec (GF := GF) (hG := hG) := by
  intro l ls
  wp_start as Hlog
  wp_auto
  wp_apply wp_raftLog_lastIndex _ ls $$ [$Hlog]
    as %li ⟨Hlog, %Hli⟩
  have Hb : uint.Z ls.prev.index' ≤ uint.Z li ∧
      uint.Z li ≤ uint.Z ls.prev.index' + (ls.sents.length : Int) + (ls.uents.length : Int) := by
    omega
  ihave ⟨%Hfl, Hlog⟩ := ownRaftLog_fl $$ Hlog
  -- `raftLog.term`'s triple is total (`Spec/raftLog__term.lean`); here the index is
  -- `lastIndex`, so the in-range clause of its postcondition applies and the error is
  -- `nil` -- which is what makes the `Panicf` on the next line unreachable.
  wp_apply wp_raftLog_term _ ls li $$ [$Hlog]
    as %t %err ⟨Hlog, %Herr, %Ht, -, -⟩
  have Herr' := Herr.2 Hb (by omega)
  subst Herr'
  have Ht' := Ht rfl
  wp_auto
  ihave ⟨%Hwf, Hlog⟩ := ownRaftLog_wf $$ Hlog
  iapply HΦ $$ %(entryID.mk t li)
  iframe Hlog
  ipureintro
  apply plogLast_eq _ _ _ _ Hwf _ Ht'
  simp only [plogLastIndexZ, List.length_append] at Hli ⊢
  push_cast; omega

end proof

end EtcdGrove
end Perennial
