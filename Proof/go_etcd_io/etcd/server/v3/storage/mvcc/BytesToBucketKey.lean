/-
Proof of `Spec/.../mvcc/BytesToBucketKey.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BytesToBucketKey
public import Spec.encoding.binary.bigEndian__Uint64
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.isTombstone

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.BytesToBucketKey.wp_proof
    (hGet : binary.bigEndian.Uint64.spec (GF := GF) (hG := hG))
    (hIs : mvcc.isTombstone.spec (GF := GF) (hG := hG)) :
    mvcc.BytesToBucketKey.spec (GF := GF) (hG := hG) := by
  intro s r rest dq hrest hm hs
  wp_start as Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  (try wp_auto)
  have hL := mvcc.revBytes_rest_length r rest
  have hlenZ : sint.Z s.len = 17 + rest.length := by
    have h1 := Hlen.1; rw [hL] at h1; have h2 := Hlen.2
    unfold sint.nat sint.Z at *; omega
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  have hl : s.len = W64 17 ∨ s.len = W64 18 := by
    rcases Nat.lt_or_ge rest.length 1 with h | h
    · left; have : rest.length = 0 := by omega
      rw [this] at hlenZ; word
    · right; have : rest.length = 1 := by omega
      rw [this] at hlenZ; word
  have h8z : sint.Z (W64 8) = 8 := by decide
  have h8z' : sint.Z (8#64 : w64) = 8 := by decide
  have h9z : sint.Z (W64 9) = 9 := by decide
  have h0z : sint.Z (W64 0) = 0 := by decide
  -- the length check
  rcases hl with hl | hl <;> simp (config := { decide := true }) only [hl]
  all_goals
    (try wp_auto)
    (try simp (config := { decide := true }) only [hl])
    (try wp_auto)
    -- the separator
    have Hb8 : 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) < sint.Z s.len :=
      ⟨by decide, by rw [hlenZ, h8z]; omega⟩
    (try simp only [Hb8, _root_.and_self, ite_true])
    wp_apply wp_load_slice_index s (sint.Z (W64 8)) _ dq (W8 95) (by decide) $$ [$Hs] as Hs
    · ipureintro; rw [h8z]; exact mvcc.revBytes_rest_getElem8 r rest
    (try wp_auto)
    -- `bytes[0:8]`: the main revision
    have Hsb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ sint.Z s.cap :=
      ⟨by decide, by decide, by rw [h8z]; have := Hwf.2; rw [hlenZ] at this; omega⟩
    (try simp only [Hsb0, _root_.and_self, ite_true])
    icases (ownSlice_slice (W64 0) (W64 8) s dq _
      ⟨by decide, by decide, by rw [h8z, hlenZ]; omega⟩).1 $$ Hs with ⟨-, H1, H2⟩
    rw [show sint.nat (W64 0) = 0 by decide, show sint.nat (W64 8) = 8 by decide,
      mvcc.revBytes_rest_subslice8]
    wp_apply (wp_beUint64 hGet (slice.slice s w8 (W64 0) (W64 8)) r.main dq) $$ [$H1] as H1
    (try wp_auto)
    ihave Hs := ownSlice_combine (W64 8) s dq (u64Be r.main) ((mvcc.revBytes r false ++ rest).drop 8)
      (W64 0) s.len ⟨by simp [u64Be_length]; decide, by decide, by decide, by rw [h8z, hlenZ]; omega⟩
      $$ H1 H2
    ihave Hs := (ownSlice_trivial_slice s dq _).2 $$ Hs
    rw [mvcc.revBytes_rest_join8]
    -- `bytes[9:]`: the sub revision
    have Hsb9 : 0 ≤ sint.Z (W64 9) ∧ sint.Z (W64 9) ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap :=
      ⟨by decide, by rw [h9z, hlenZ]; omega, Hwf.2⟩
    (try simp only [Hsb9, _root_.and_self, ite_true])
    icases (ownSlice_slice (W64 9) s.len s dq _
      ⟨by decide, by rw [h9z, hlenZ]; omega, Int.le_refl _⟩).1 $$ Hs with ⟨H0, H1, -⟩
    rw [show sint.nat (W64 9) = 9 by decide, ← Hlen.1, mvcc.revBytes_rest_subslice9]
    wp_apply (hGet (slice.slice s w8 (W64 9) s.len) (u64Be r.sub) rest dq (u64Be_length _)) $$ [$H1] as H1
    (try wp_auto)
    ihave Hs := ownSlice_combine (W64 9) s dq ((mvcc.revBytes r false ++ rest).take 9)
      (u64Be r.sub ++ rest) (W64 0) s.len
      ⟨by rw [List.length_take, mvcc.revBytes_rest_length,
            show sint.nat (W64 9) - sint.nat (W64 0) = 9 by decide]; omega,
        by decide, by decide, by rw [h9z, hlenZ]; omega⟩ $$ H0 H1
    ihave Hs := (ownSlice_trivial_slice s dq _).2 $$ Hs
    rw [mvcc.revBytes_rest_join9]
    simp only [beToU64_u64Be]
    (try wp_auto)
    -- neither revision is negative
    rw [show (decide (sint.Z r.main < sint.Z (W64 0)) : Bool) = false by
      rw [h0z, decide_eq_false_iff_not]; omega]
    (try wp_auto)
    (try rw [show (decide (sint.Z r.sub < sint.Z (W64 0)) : Bool) = false by
      rw [h0z, decide_eq_false_iff_not]; omega])
    (try wp_auto)
    -- the bucket key
    wp_apply (hIs s _ dq) $$ [$Hs] as Hs
    (try wp_auto)
    rw [mvcc.isTomb_revBytes, show Revision.mk r.main r.sub = mvcc.revVal r from rfl]
    iapply HΦ $$ Hs

end proof

end EtcdGrove
end Perennial
