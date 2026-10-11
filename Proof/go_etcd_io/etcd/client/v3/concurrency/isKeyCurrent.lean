/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/isKeyCurrent.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.isKeyCurrent
public import Spec.go_etcd_io.etcd.client.v3.ModRevision
public import Spec.go_etcd_io.etcd.client.v3.Compare

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem isKeyCurrent.wp_proof (hMR : EtcdGrove.ModRevision.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG)) :
    isKeyCurrent.spec (GF := GF) (hG := hG) := by
  intro pfx k p e
  wp_start as #Hr
  unfold readRespAt
  icases Hr with ⟨%Hpn, -, -, %sl, %ps, #Hsl, #Hps, #Hkvs⟩
  ihave %Hlen := ownSlice_len $$ Hps
  iunfold kvPtrsAt at Hkvs
  icases Hkvs with ⟨%Hl, #Hkv⟩
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_auto
  unfold readCmp ReadM.modRev
  rcases He : e.kv with _ | w
  all_goals simp only [He, Option.toList] at Hl ⊢
  · have Hlen0 : sl.len = W64 0 := by
      have : ps.length = 0 := by simpa using Hl
      rw [this] at Hlen; word
    rw [Hlen0]
    wp_auto
    wp_apply hMR k $$ [$Hcv] as %c0 #Hc0
    (try wp_auto)
    wp_apply hCmp c0 _ go!"=" .eq _ (.num (W64 0)) $$ [$Hcv $Hc0] as %c1 #Hc1
    · ipureintro
      refine ⟨by simp [cmpOpOf], ?_⟩
      simp [cmpKeyM, cmpArgOf]
    (try wp_auto)
    iapply HΦ $$ Hc1
  · obtain ⟨kp, rfl⟩ : ∃ kp, ps = [kp] := by
      match ps, Hl with
      | [kp], _ => exact ⟨kp, rfl⟩
    have Hlen1 : sl.len ≠ W64 0 := by
      intro h; rw [h] at Hlen; simp at Hlen; revert Hlen; decide
    rw [show decide (sl.len = W64 0) = false by simpa using Hlen1]
    wp_auto
    ihave #Hw := Hkv $$ %0 %kp %w %rfl %(by simp)
    iunfold kvValAt at Hw
    icases Hw with ⟨%keySl, %valSl, -, -, -, #Hmr, -⟩
    wp_apply hMR k $$ [$Hcv] as %c0 #Hc0
    (try wp_auto)
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len by simp at Hlen; word)]
    icases ownSlice_elem_acc (sint.Z (W64 0)) kp sl DFrac.discard [kp] (by word) (by simp)
      $$ Hps with ⟨#Hkpe, -⟩
    wp_auto
    wp_apply hCmp c0 _ go!"=" .eq _ (.num w.modRev) $$ [$Hcv $Hc0] as %c1 #Hc1
    · ipureintro
      refine ⟨by simp [cmpOpOf], ?_⟩
      simp [cmpKeyM, cmpArgOf]
    (try wp_auto)
    iapply HΦ $$ Hc1

end proof

end concurrency
end EtcdGrove
end Perennial
