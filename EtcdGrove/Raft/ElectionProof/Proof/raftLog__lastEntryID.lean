/-
Port of `election_proof/proof_raftLog__lastEntryID.v`.
-/
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__lastEntryID
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__lastIndex
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__term

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

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] [GoGlobalContext] in
/-- Rocq `plog_last_eq`: on a well-formed log, the id read off `lastIndex()` and the
term there is `plogLast`. -/
private theorem plogLast_eq (b : entryID) (es : List raftpb.Entry) (t li : w64)
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
  obtain ⟨prev, sents, uents, lcm, lap, snap⟩ := ls
  wp_start as Hlog
  wp_auto
  wp_apply wp_raftLog_lastIndex _ ⟨prev, sents, uents, lcm, lap, snap⟩ $$ [$Hlog]
    as %li ⟨Hlog, %Hli⟩
  have Hb : uint.Z prev.index' ≤ uint.Z li ∧
      uint.Z li ≤ uint.Z prev.index' + (sents.length : Int) + (uents.length : Int) := by
    simp only at Hli; omega
  -- `raftLog.term`'s triple is total (`Spec/raftLog__term.lean`); here the index is
  -- `lastIndex`, so the in-range clause of its postcondition applies and the error is
  -- `nil` -- which is what makes the `Panicf` on the next line unreachable.
  wp_apply wp_raftLog_term _ ⟨prev, sents, uents, lcm, lap, snap⟩ li $$ [$Hlog]
    as %t %err ⟨Hlog, %Herr, %Ht, -⟩
  have Herr' := Herr.2 Hb
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
