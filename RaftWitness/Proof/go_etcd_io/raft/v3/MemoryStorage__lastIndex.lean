/-
Port of `election_proof/proof_MemoryStorage__lastIndex.v`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.MemoryStorage__lastIndex
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasMemstorage

@[expose] public section

set_option linter.unusedSectionVars false

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

/-- Read through the dummy entry `ents[0]` (a read-only log entry, `entsRO`) with
`GetIndex()` (raft v3.7). The sum does not wrap: `Hb`. -/
theorem MemoryStorage.lastIndex.wp_proof
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG)) :
    MemoryStorage.lastIndex.spec (GF := GF) (hG := hG) := by
  intro ms σ Hb
  wp_start as Hf
  iNamed Hf
  iNamed Hf
  ihave %Hcl := entsRO_cons_len $$ Hents
  icases entsRO_lookup es (dummy :: σ.ents) 0 dummy rfl $$ Hents
    with ⟨%ls, %l0, #Hls, #He0, %Hl0⟩
  wp_auto
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es (sint.Z (W64 0)) ls DFrac.discard l0 (by word) $$ [Hls] with -
  · iframe Hls; ipureintro; exact Hl0.1
  wp_apply wp_GetIndex.1 l0 DFrac.discard dummy $$ [He0] with -
  · iframe He0
  iapply HΦ
  isplitr
  · ipureintro
    rw [Hdummy.1]
    word
  · unfold memstorageFields
    iexists hp, es, dummy, nfi, nli, nen, nte, nsn
    iframe
    ipureintro
    exact Hdummy

end proof

end EtcdGrove
end Perennial
