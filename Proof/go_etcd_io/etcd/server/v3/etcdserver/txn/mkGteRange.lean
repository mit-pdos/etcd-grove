/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.mkGteRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.mkGteRange.wp_proof : txn.mkGteRange.spec (GF := GF) (hG := hG) := by
  intro rangeEnd e
  wp_start as #He
  ihave %Hlen := ownSlice_len _ _ _ $$ He
  wp_auto
  wp_if_destruct
  · -- `len(rangeEnd) == 1`: the one byte
    have h1 : e.length = 1 := by rw [Hlen.1, Hif]; rfl
    obtain ⟨b, rfl⟩ : ∃ b, e = [b] := by
      match e, h1 with
      | [b], _ => exact ⟨b, rfl⟩
    have hb : 0 ≤ sint.Z (W64 0 : w64) ∧ sint.Z (W64 0 : w64) < sint.Z rangeEnd.len := by
      rw [Hif]; decide
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index rangeEnd (sint.Z (W64 0 : w64)) [b] DFrac.discard b (by decide)
      $$ [$He] as -
    · ipureintro; rfl
    (try wp_auto)
    wp_if_destruct
    · -- `[0]`: the empty, non-nil slice
      wp_apply txn.wp_slice_literal_nn (V := w8) []
      isplitr
      · ipureintro; rfl
      iintro %sl %Hnn ⟨Hsl, -⟩
      ipersist Hsl
      (try wp_auto)
      iapply HΦ
      iframe Hsl
      ipureintro
      intro h
      first
        | (injection h with h1; exact Hnn h1)
        | (unfold slice.nil at h; injection h with h1; exact Hnn h1)
    · -- another byte: the range end as it is
      have hne : [b] ≠ [W8 0] := fun h => Hif (by simpa using h)
      (try wp_auto)
      iapply HΦ
      simp only [hne, ↓reduceIte]
      iframe He
  · -- another length: the range end as it is
    have hne : e ≠ [W8 0] := by
      intro h; subst h
      apply Hif
      have h2 := mvcc.W64_sint_nat rangeEnd.len Hlen.2
      rw [← Hlen.1] at h2
      rw [← h2]; rfl
    iapply HΦ
    simp only [hne, ↓reduceIte]
    iframe He

end proof

end EtcdGrove
end Perennial
