/-
Proof of `Spec/WatchResponse__IsProgressNotify.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__IsProgressNotify
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader__GetRevision

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

-- Loads from the fractional response: the field-store `AccessStrict` instances (which need
-- `DFrac.own 1`) are found first and the search does not backtrack.
attribute [-instance] go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_Header
  go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_Events
  go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_CompactRevision
  go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_Canceled
  go_etcd_io.etcd.client.v3.WatchResponse.WatchResponse_access_store_Created

theorem WatchResponse.IsProgressNotify.wp_proof
    (wp_GetRevision : ResponseHeader.GetRevision.spec (GF := GF) (hG := hG)) :
    WatchResponse.IsProgressNotify.spec (GF := GF) (hG := hG) := by
  intro wr resp r dq
  obtain ⟨events, compactRev, canceled, created, hdrRev⟩ := r
  simp only [respAt, eventsAt]
  wp_start as ⟨Hwr, ⟨⟨%ls, #Hsl, %Hlen, #Hall⟩, #Hhdr, %Hf⟩⟩
  ihave %Hsl_len := ownSlice_len _ _ _ $$ Hsl
  obtain ⟨Hc, Hca, Hcr⟩ := Hf
  have Hev : (resp.Events'.len = W64 0) ↔ events = [] := by
    rw [← List.length_eq_zero_iff, ← Hlen]; constructor <;> intro h <;> word
  simp only [RespModel.isProgressNotify]
  wp_auto
  wp_if_destruct
  · rw [Hca]
    rw [show events.isEmpty = true from List.isEmpty_iff.2 (Hev.1 Hif)]
    cases canceled
    · wp_auto
      rw [Hcr]
      cases created
      · wp_auto
        rw [Hc]
        wp_if_destruct
        · wp_apply wp_GetRevision $$ [$Hhdr]
          simp only [Bool.true_and, Bool.and_true, Bool.not_false, Bool.not_true, Bool.false_and, Bool.and_false, _root_.decide_true]
          wp_end
        · simp only [Bool.true_and, Bool.and_true, Bool.not_false, Bool.not_true, Bool.false_and, Bool.and_false, _root_.decide_true]
          wp_end
      · wp_auto; simp only [Bool.true_and, Bool.and_true, Bool.not_false, Bool.not_true, Bool.false_and, Bool.and_false, _root_.decide_true]; wp_end
    · wp_auto; simp only [Bool.true_and, Bool.and_true, Bool.not_false, Bool.not_true, Bool.false_and, Bool.and_false, _root_.decide_true]; wp_end
  · rw [show events.isEmpty = false from by
      cases events
      · exact absurd (Hev.2 rfl) Hif
      · rfl]
    simp only [Bool.true_and, Bool.and_true, Bool.not_false, Bool.not_true, Bool.false_and, Bool.and_false, _root_.decide_true]
    wp_end

end proof

end EtcdGrove
end Perennial
