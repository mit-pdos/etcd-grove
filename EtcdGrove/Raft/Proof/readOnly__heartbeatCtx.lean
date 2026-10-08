/-
Port of election_proof/proof_readOnly__heartbeatCtx.v.
-/
import EtcdGrove.Raft.Spec.readOnly__heartbeatCtx

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

/-- The length test is `pending = []` (`Hreqs` ties the queue to it); the
other exit makes the eight bytes and fills them in. -/
theorem readOnly.heartbeatCtx.wp_proof :
    readOnly.heartbeatCtx.spec (GF := GF) (hG := hG) := by
  intro ro r
  wp_start as H
  iNamed H
  iunfold ownReadOnly at Hown
  icases Hown with ⟨%rov, %ptrs, Hown⟩
  iNamed Hown
  ihave %Hl := ownSlice_len $$ Hucr
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hreqs
  wp_auto
  wp_if_destruct
  · have Hnil : r.pending = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← Hlen, Hl.1]; word
    iapply HΦ
    isplitl [Hro Hacks Hucr Hucr_cap Hreqs]
    · unfold ownReadOnly
      iexists rov, ptrs
      iframe
      ipureintro; exact ⟨Hro_safe, Hro_conf⟩
    ileft
    ipureintro; exact ⟨Hnil, rfl⟩
  · have Hne : r.pending ≠ [] := by
      intro Hnil
      rw [Hnil] at Hlen
      apply Hif
      simp only [List.length_nil] at Hlen
      rw [Hlen] at Hl
      word
    wp_apply wp_slice_make2 (V := w8) as %sl ⟨Hsl, Hcap⟩
    · ipureintro; word
    have Hpos : rov.confirmedReads' + rov.unconfirmedReads'.len = readonlyPosition r := by
      unfold readonlyPosition
      rw [← Hro_conf, ← Hlen, Hl.1]
      word
    rw [Hpos]
    wp_apply encoding.binary.wp_LittleEndian_PutUint64 sl
      (List.replicate 8 (zero_val w8)) [] (readonlyPosition r) rfl $$ [Hsl] as Hsl
    · rw [List.append_nil]; iexact Hsl
    iapply HΦ
    isplitl [Hro Hacks Hucr Hucr_cap Hreqs]
    · unfold ownReadOnly
      iexists rov, ptrs
      iframe
      ipureintro; exact ⟨Hro_safe, Hro_conf⟩
    iright
    rw [List.append_nil] at *
    iframe
    ipureintro; exact Hne

end proof

end EtcdGrove
end Perennial
