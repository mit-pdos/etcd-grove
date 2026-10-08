/- Port of election_proof/proof_MemoryStorage__firstIndex.v. -/
import EtcdGrove.Raft.Spec.MemoryStorage__firstIndex

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

/-- `ents[0].Index + 1`, read through the dummy entry. The slice is read-only (`↦*□`),
so the element access is the one `limitSize` uses (`ownSlice_elem_acc`) and the entry
is handed back at once. The sum does not wrap: `Hb`. -/
theorem MemoryStorage.firstIndex.wp_proof :
    MemoryStorage.firstIndex.spec (GF := GF) (hG := hG) := by
  intro ms prev ents ss Hb
  wp_start as H
  iNamed H
  unfold memstorageFields
  iNamed Hf
  wp_alloc ms_ptr as ms; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear ms
  ihave %Hlen := ownSlice_len $$ Hents
  simp only [List.length_cons] at Hlen
  simp only [show (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z es.len) = True from
    eq_true (by word), ↓reduceIte]
  icases ownSlice_elem_acc (sint.Z (W64 0)) dummy _ _ _ (by word) (by simp) $$ Hents with ⟨#He, Hback⟩
  ihave Hents := Hback $$ %dummy He
  rw [show (dummy :: ents).set (sint.Z (W64 0)).toNat dummy = dummy :: ents by simp]
  iStructNamed He
  wp_pures; wp_load; wp_pures
  iapply HΦ
  isplitr
  · ipureintro
    rw [Hdummy.1]
    word
  · iexists hs, snap, es, dummy, cs, voters
    iframe
    ipureintro
    exact ⟨Hsnap_id, Hdummy⟩

end proof

end EtcdGrove
end Perennial
