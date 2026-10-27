/-
Lean-first (no Rocq counterpart).

The proof of `kvFromTxnResponse`: `GetResponseRange`, then the range response's one key-value.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kubernetes.kvFromTxnResponse
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseRange

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kubernetes

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.kubernetes.Assumptions]

theorem kvFromTxnResponse.wp_proof
    (wp_GRR : EtcdGrove.ResponseOp.GetResponseRange.spec (GF := GF) (hG := hG)) :
    kvFromTxnResponse.spec (GF := GF) (hG := hG) := by
  intro p rev kvs more count
  wp_start as #Hm
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  simp only [opRespMsg]
  icases Hm with ⟨%Hpn, %w, %r, #Hresp, #Hrr, #Hr⟩
  wp_auto
  wp_apply wp_GRR p w r $$ []
  · iframe #
    ipureintro; exact Hpn
  iunfold txn.rangeResponseIs at Hr
  icases Hr with ⟨%Hrn, %h, %sl, %ps, #Hh, %Hhn, #Hrev, #Hkvf, #Hsl, #Hkvs, #Hmore, #Hcount⟩
  iunfold txn.kvsIs at Hkvs
  icases Hkvs with ⟨%Hlen, #Hall⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_if_destruct
  · obtain ⟨v, hv⟩ : ∃ v, kvs = [v] := by
      match kvs, Hlen with
      | [v], _ => exact ⟨v, rfl⟩
      | [], h => exfalso; simp at h; rw [h] at Hsll; simp at Hsll; word
      | _ :: _ :: _, h => exfalso; rw [h] at Hsll; simp at Hsll; word
    subst hv
    obtain ⟨p0, Hp0⟩ : ∃ p0, ps[0]? = some p0 := by
      have : 0 < ps.length := by rw [Hlen]; simp
      exact ⟨ps[0], List.getElem?_eq_getElem this⟩
    ihave #Hkv := Hall $$ %0 %p0 %v %Hp0 %rfl
    have Hbnd0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
      have := Hsll.1
      constructor <;> word
    simp only [Hbnd0, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd0.1 $$ [Hsl] as -
    · iframe Hsl; ipureintro; exact Hp0
    iapply HΦ
    rw [show single [v] = some v from rfl]
    iapply kvOut_some
    iexact Hkv
  · iapply HΦ
    have : single kvs = none := by
      match kvs, Hlen with
      | [v], h => exfalso; apply Hif; rw [h] at Hsll; simp at Hsll; word
      | [], _ => rfl
      | _ :: _ :: _, _ => rfl
    rw [this]
    simp only [kvOut]
    ipureintro; first | rfl | trivial

end proof

end kubernetes
end EtcdGrove
end Perennial
