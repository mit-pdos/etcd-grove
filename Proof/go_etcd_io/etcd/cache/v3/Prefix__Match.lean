/-
Proof of `Spec/go_etcd_io/etcd/cache/v3/Prefix__Match.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Prefix__Match

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Prefix.Match.wp_proof : Prefix.Match.spec (GF := GF) (hG := hG) :=
    fun pfx sl key dq => by
  wp_start as Hsl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_if_destruct
  · simp only [List.nil_prefix, decide_true]
    iapply HΦ $$ Hsl
  try wp_auto
  wp_func_call
  try wp_auto
  by_cases hl : pfx.length < 2 ^ 63
  rotate_left
  · simp only [hl, ↓reduceIte]
    wp_apply wp_AngelicExit
  simp only [hl, ↓reduceIte]
  wp_auto
  have hn : sint.Z (W64 (pfx.length : Int)) = pfx.length := by
    have : (pfx.length : Int) < 2 ^ 63 := by exact_mod_cast hl
    word
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
  wp_if_destruct
  · have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 (pfx.length : Int)) ∧
        sint.Z (W64 (pfx.length : Int)) ≤ sint.Z sl.len := by
      refine ⟨by decide, by rw [hn]; simp, by omega⟩
    have hb' : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 (pfx.length : Int)) ∧
        sint.Z (W64 (pfx.length : Int)) ≤ sint.Z sl.cap := ⟨hb.1, hb.2.1, by omega⟩
    simp only [hb', and_self, ↓reduceIte]
    icases (ownSlice_slice (W64 0) (W64 (pfx.length : Int)) sl dq key hb).1 $$ Hsl
      with ⟨H0, Hmid, Hrest⟩
    wp_apply wp_bytes_to_string _ _ dq $$ [$Hmid] as Hmid
    try wp_auto
    ihave Hsl := (ownSlice_slice (W64 0) (W64 (pfx.length : Int)) sl dq key hb).2 $$ [H0 Hmid Hrest]
    · iframe
    have hn' : sint.nat (W64 (pfx.length : Int)) = pfx.length := by
      have : sint.nat (W64 (pfx.length : Int)) = (sint.Z (W64 (pfx.length : Int))).toNat := rfl
      rw [this, hn]; simp
    have he : decide (subslice 0 (sint.nat (W64 (pfx.length : Int))) key = pfx) =
        decide (pfx <+: key) := by
      rw [hn']
      simp only [subslice, List.drop_zero, Nat.sub_zero]
      rw [decide_eq_decide]
      constructor
      · intro h; rw [← h]; exact List.take_prefix _ _
      · intro h; rw [List.prefix_iff_eq_take] at h; exact h.symm
    rw [he]
    iapply HΦ $$ Hsl
  · have hnp : ¬ pfx <+: key := by
      intro h
      have := h.length_le
      have : (pfx.length : Int) ≤ sint.Z sl.len := by
        have h2 : (key.length : Int) = sint.Z sl.len := by
          rw [Hlen.1]; exact Int.toNat_of_nonneg Hlen.2
        omega
      exact Hif (by rw [hn]; exact this)
    simp only [hnp, decide_false]
    iapply HΦ $$ Hsl

end proof

end EtcdGrove
end Perennial
