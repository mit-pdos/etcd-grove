/-
Port of `election_proof/proof_MemoryStorage__lastIndex.v`.
-/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__lastIndex

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

/-- `ents[0].Index + len(ents) - 1`, read through the dummy entry. The slice is
read-only (`↦*□`), so the element access is the one `limitSize` uses
(`ownSlice_elem_acc`) and the entry is handed back at once. The sum does not wrap:
`Hb`. -/
theorem MemoryStorage.lastIndex.wp_proof : MemoryStorage.lastIndex.spec (GF := GF) (hG := hG) := by
  intro ms σ Hb
  wp_start as Hf
  iNamed Hf
  iNamed Hf
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hents
  simp only [List.length_cons] at Hlen
  simp only [show (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z es.len) = True from
    eq_true (by word), ↓reduceIte]
  icases ownSlice_elem_acc (sint.Z (W64 0)) dummy es _ _ (by word) rfl $$ Hents
    with ⟨#He, Hback⟩
  ihave Hents := Hback $$ %dummy He
  rw [show (dummy :: σ.ents).set (sint.Z (W64 0)).toNat dummy = dummy :: σ.ents by simp]
  -- Lean: `wp_load` does not find the field `Access` instance of a struct points-to at
  -- `DFrac.discard`, so split the (persistent) entry into its fields.
  iStructNamed He
  wp_auto
  iapply HΦ
  isplitr
  · ipureintro
    rw [← Hdummy.1]
    word
  · unfold memstorageFields
    iexists hs, snap, es, dummy, nfi, nli, nen, nte, nsn, voters
    iframe
    ipureintro
    exact ⟨Hsnap_id, Hdummy⟩

end proof

end EtcdGrove
end Perennial
