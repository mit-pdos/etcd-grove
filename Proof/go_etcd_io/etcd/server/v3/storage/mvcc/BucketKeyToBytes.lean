/-
Proof of `Spec/.../mvcc/BucketKeyToBytes.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BucketKeyToBytes
public import Spec.encoding.binary.bigEndian__PutUint64

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

theorem mvcc.BucketKeyToBytes.wp_proof
    (hPut : binary.bigEndian.PutUint64.spec (GF := GF) (hG := hG)) :
    mvcc.BucketKeyToBytes.spec (GF := GF) (hG := hG) := by
  intro bk s bs hlen
  wp_start as ⟨Hs, Hcap⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hcapwf := ownSliceCap_wf _ _ $$ Hcap
  (try wp_auto)
  have hbs : 17 ≤ bs.length := by omega
  have hlenZ : sint.Z s.len = bs.length := by
    rw [Hlen.1]; unfold sint.nat sint.Z; have := Hlen.2; unfold sint.Z at this; omega
  have h8z : sint.Z (W64 8) = 8 := by decide
  have h9z : sint.Z (W64 9) = 9 := by decide
  have h8z' : sint.Z (8#64 : w64) = 8 := by decide
  have h9z' : sint.Z (9#64 : w64) = 9 := by decide
  -- `binary.BigEndian.PutUint64(bytes, uint64(rev.Main))`
  rw [← List.take_append_drop 8 bs]
  wp_apply (hPut s (bs.take 8) (bs.drop 8) bk.Revision'.Main'
    (by simp [List.length_take]; omega)) $$ [Hs] as Hs
  · iexact Hs
  rw [List.take_append_drop]
  (try wp_auto)
  -- `bytes[8] = '_'`
  have Hb8 : 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) < sint.Z s.len :=
    ⟨by decide, by rw [hlenZ, h8z]; omega⟩
  simp only [Hb8, _root_.and_self, ite_true]
  wp_apply wp_store_slice_index (V := w8) (t := go.byte) s _ _ (W8 95) $$ [$Hs] as Hs
  · ipureintro; simp [u64Be_length, h8z']; omega
  (try wp_auto)
  (try simp only [show (sint.Z (W64 8)).toNat = 8 by decide])
  rw [mvcc.enc_step1 _ bs (by omega)]
  -- `bytes[9:]`: the bytes from 9
  have Hsb : 0 ≤ sint.Z (W64 9) ∧ sint.Z (W64 9) ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap :=
    ⟨by decide, by rw [hlenZ, h9z]; omega, Hcapwf.2⟩
  simp only [Hsb, _root_.and_self, ite_true]
  icases (ownSlice_slice (W64 9) s.len s (DFrac.own 1) _
    ⟨by decide, by rw [hlenZ, h9z]; omega, Int.le_refl _⟩).1 $$ Hs with ⟨Hpre, Hmid, -⟩
  have hn9 : sint.nat s.len = 9 + (bs.drop 9).length := by
    rw [← Hlen.1, List.length_drop]; omega
  rw [hn9, show sint.nat (W64 9) = 9 by decide, mvcc.enc_subslice9, mvcc.enc_take9]
  -- `binary.BigEndian.PutUint64(bytes[9:], uint64(rev.Sub))`
  (try wp_auto)
  rw [← List.take_append_drop 8 (bs.drop 9)]
  wp_apply (hPut (slice.slice s w8 (W64 9) s.len) ((bs.drop 9).take 8) ((bs.drop 9).drop 8)
    bk.Revision'.Sub' (by simp [List.length_take, List.length_drop]; omega)) $$ [Hmid] as Hmid
  · iexact Hmid
  rw [List.drop_drop]
  (try wp_auto)
  -- the whole buffer again
  ihave Hs := ownSlice_combine (W64 9) s (DFrac.own 1) (u64Be bk.Revision'.Main' ++ [W8 95])
    (u64Be bk.Revision'.Sub' ++ bs.drop (9 + 8)) (W64 0) s.len
    ⟨by simp [u64Be_length]; decide, by decide, by decide, by rw [h9z, hlenZ]; omega⟩ $$ Hpre Hmid
  ihave Hs := (ownSlice_trivial_slice s (DFrac.own 1) _).2 $$ Hs
  simp only [List.append_assoc, List.singleton_append, show 9 + 8 = 17 from rfl]
  rw [← mvcc.revBytes_revOf_eq bk.Revision' (bs.drop 17)]
  -- `if rev.tombstone`
  (try wp_auto)
  cases htomb : bk.tombstone' with
  | true =>
    -- the mark: appended to 17 bytes, over the 18th
    (try wp_auto)
    wp_if_destruct
    · -- 17 bytes: `bytes = append(bytes, markTombstone)`
      have h17 : bs.length = 17 := by rw [Hlen.1, Hif]; decide
      rw [List.drop_of_length_le (by omega), List.append_nil]
      wp_apply wp_slice_literal (l := [W8 116])
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, Hslcap⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s' ⟨Hs, Hcap, -⟩
      (try wp_auto)
      iapply HΦ
      rw [mvcc.bucketKeyBytes_true, mvcc.revBytes_true]
      iframe Hs Hcap
    · (try wp_auto)
      wp_if_destruct
      · -- 18 bytes: `bytes[17] = markTombstone`
        have h18 : bs.length = 18 := by rw [Hlen.1, Hif]; decide
        have h17z : sint.Z (W64 17) = 17 := by decide
        have h17z' : sint.Z (17#64 : w64) = 17 := by decide
        have hd : bs.drop 17 = [bs[17]] := by
          rw [List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega)]
        rw [hd]
        have Hb17 : 0 ≤ sint.Z (W64 17) ∧ sint.Z (W64 17) < sint.Z s.len :=
          ⟨by decide, by rw [Hif]; decide⟩
        simp only [Hb17, _root_.and_self, ite_true]
        wp_apply wp_store_slice_index (V := w8) (t := go.byte) s _ _ (W8 116) $$ [$Hs] as Hs
        · ipureintro; simp [mvcc.revBytes_false_length, h17z']
        (try wp_auto)
        iapply HΦ
        (try simp only [show (sint.Z (W64 17)).toNat = 17 by decide])
        rw [mvcc.bucketKeyBytes_set17]
        iframe Hs Hcap
      · -- neither: the buffer has 17 or 18 bytes
        exfalso
        rcases hlen with h | h
        · exact ‹¬s.len = W64 17› (by rw [h] at hlenZ; word)
        · exact Hif (by rw [h] at hlenZ; word)
  | false =>
    (try wp_auto)
    iapply HΦ
    rw [mvcc.bucketKeyBytes_false]
    iframe Hs Hcap

end proof

end EtcdGrove
end Perennial
