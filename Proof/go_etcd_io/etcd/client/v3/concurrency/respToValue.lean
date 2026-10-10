/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/respToValue.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.respToValue

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem respToValue.wp_proof : respToValue.spec (GF := GF) (hG := hG) := by
  intro p v
  wp_start as H
  icases H with (%Hnil | ⟨%pfx, %k, %e, #Hr, %Hv⟩)
  · obtain ⟨rfl, rfl⟩ := Hnil
    wp_auto
    iapply HΦ
    ipureintro; trivial
  · unfold readRespAt
    icases Hr with ⟨%Hpn, -, -, %sl, %ps, #Hsl, #Hps, #Hkvs⟩
    ihave %Hlen := ownSlice_len $$ Hps
    iunfold kvPtrsAt at Hkvs
    icases Hkvs with ⟨%Hl, #Hkv⟩
    wp_auto
    rw [show decide (p = null) = false by simpa using Hpn]
    wp_auto
    subst Hv
    rcases He : e.kv with _ | w
    all_goals simp only [He, Option.toList, ReadM.value] at Hl ⊢
    · have Hlen0 : sl.len = W64 0 := by
        have : ps.length = 0 := by simpa using Hl
        rw [this] at Hlen; word
      rw [Hlen0]
      wp_auto
      iapply HΦ
      ipureintro; trivial
    · obtain ⟨kp, rfl⟩ : ∃ kp, ps = [kp] := by
        match ps, Hl with
        | [kp], _ => exact ⟨kp, rfl⟩
      have Hlen1 : sl.len ≠ W64 0 := by
        intro h; rw [h] at Hlen; simp at Hlen; revert Hlen; decide
      rw [show decide (sl.len = W64 0) = false by simpa using Hlen1]
      wp_auto
      ihave #Hw := Hkv $$ %0 %kp %w %rfl %(by simp)
      iunfold kvValAt at Hw
      icases Hw with ⟨%keySl, %valSl, -, -, -, -, -, #Hval, #Hvs, -⟩
      rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len by simp at Hlen; word)]
      icases ownSlice_elem_acc (sint.Z (W64 0)) kp sl DFrac.discard [kp] (by word) (by simp)
        $$ Hps with ⟨#Hkpe, -⟩
      wp_auto
      wp_apply wp_bytes_to_string $$ Hvs as -
      (try wp_auto)
      iapply HΦ
      ipureintro; trivial

end proof

end concurrency
end EtcdGrove
end Perennial
