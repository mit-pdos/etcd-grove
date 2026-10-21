/-
Lemmas of the proofs of `raftLog`'s reads (raft v3.7 retarget, stage R3): the slice facts of
`InvRaftlog.lean` and Perennial's `ownSlice_*` restated for an entry slice `entsPts`
(`InvPbLog.lean`).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRaftlog

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ownSlice_wf` of an entry slice. -/
theorem entsPts_wf (s : GoSlice) (dq : DFrac) (es : List EntryM) :
    entsPts (GF := GF) s dq es ⊢ ⌜0 ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap⌝ := by
  iintro H
  iunfold entsPts at H
  icases H with ⟨%ls, Hs, -⟩
  iapply ownSlice_wf $$ Hs

/-- `ownSlice_same_ptr_len` (`InvRaftlog.lean`) of a non-empty entry slice: a three-index
re-slice `s[0:len:len]` holds the same entries. -/
theorem entsPts_same_ptr_len (s1 s2 : GoSlice) (dq : DFrac) (es : List EntryM) :
    es ≠ [] →
    s1.ptr = s2.ptr →
    s1.len = s2.len →
    sint.Z s2.len ≤ sint.Z s2.cap →
    ⊢ entsPts (GF := GF) s1 dq es -∗ entsPts s2 dq es := by
  intro Hne Hptr Hlen Hcap
  iintro H
  iunfold entsPts at H
  icases H with ⟨%ls, Hs, Hb⟩
  ihave %Hl := entsBig_length $$ Hb
  have Hnl : ls ≠ [] := by
    intro h; apply Hne; rw [h] at Hl; exact List.eq_nil_of_length_eq_zero Hl.symm
  ihave Hs2 := ownSlice_same_ptr_len s1 s2 dq ls Hnl Hptr Hlen Hcap $$ Hs
  iunfold entsPts
  iexists ls
  iframe Hs2 Hb

end lemmas

end EtcdGrove
end Perennial
