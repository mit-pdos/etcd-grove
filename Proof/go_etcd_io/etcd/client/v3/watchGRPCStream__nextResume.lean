/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__nextResume.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__nextResume

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem watchGRPCStream.nextResume.wp_proof :
    watchGRPCStream.nextResume.spec (GF := GF) (hG := hG) := by
  intro wgs s l
  wp_start as ⟨Hres, Hs⟩
  wp_auto
  iunfold sliceOwn at Hs
  icases Hs with ⟨Hs, Hcap⟩
  ihave HI : (∃ (s' : GoSlice) (l' : List Loc), "Hres" ∷ wgsF wgs go!"resuming" ↦ s' ∗
      "Hs" ∷ s' ↦* l' ∗ "Hcap" ∷ ownSliceCap Loc s' (DFrac.own 1) ∗
      "%Hl" ∷ ⌜l.dropWhile (fun x => decide (x = null)) = l'.dropWhile (fun x => decide (x = null))⌝)
    $$ [Hres Hs Hcap]
  · iexists s, l; iframe; ipureintro; rfl
  wp_for HI
  ihave %Hlen := ownSlice_len $$ Hs
  wp_if_destruct
  · have Hne : s'.len ≠ W64 0 := by
      have h := GoGlobalContext.intoVal_inj_bool Hif; simpa using h
    obtain ⟨x, rest, rfl⟩ : ∃ x rest, l' = x :: rest := by
      cases l' with
      | nil => simp at Hlen; word
      | cons x rest => exact ⟨x, rest, rfl⟩
    have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s'.len := by word
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s' (sint.Z (W64 0)) (x :: rest) _ x (by word) $$ [Hs] as Hs
    · iframe; ipureintro; rfl
    wp_if_destruct
    · -- `resuming[0]` is nil: drop it
      ihave %Hcw := ownSliceCap_wf $$ Hcap
      have hb1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z s'.len ∧
          sint.Z s'.len ≤ sint.Z s'.cap := ⟨by word, by word, Hcw.2⟩
      simp only [hb1, _root_.and_self, ↓reduceIte]
      wp_auto
      wp_for_post
      icases (ownSlice_slice (W64 1) s'.len s' (DFrac.own 1) (null :: rest)
        ⟨by word, by word, by word⟩).1 $$ Hs with ⟨-, Hs, -⟩
      ihave Hcap := (ownSliceCap_slice s' (W64 1) _ ⟨by word, by word, Hcw.2⟩).1 $$ Hcap
      have Hsub : subslice (sint.nat (W64 1)) (sint.nat s'.len) (null :: rest) = rest := by
        rw [subslice_def, List.take_of_length_le (by simp at Hlen ⊢; word)]
        rfl
      rw [Hsub]
      iframe
      iexists _, rest
      iframe
      ipureintro
      rw [Hl]; simp
    · simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index s' (sint.Z (W64 0)) (x :: rest) _ x (by word) $$ [Hs] as Hs
      · iframe; ipureintro; rfl
      wp_for_post
      iapply HΦ
      have Hd : List.dropWhile (fun x => decide (x = null)) l = x :: rest := by
        rw [Hl]; simp [Hif]
      rw [Hd]
      iexists s'
      iunfold sliceOwn
      iframe
      ipureintro; rfl
  · have Hz : s'.len = W64 0 := by
      by_cases h : s'.len = W64 0
      · exact h
      · exfalso; apply Hif; congr 1; simpa using h
    have Hnil : l' = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hlen.1, Hz]; rfl
    subst Hnil
    rw [ite_eq_left_of_eq_true _ _ (by simp [Hz])]
    wp_auto
    iapply HΦ
    rw [Hl]
    iexists s'
    iunfold sliceOwn
    iframe
    ipureintro; rfl

end proof

end EtcdGrove
end Perennial
