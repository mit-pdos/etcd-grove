/-
The freelist page `freelist.Write` builds (`Commit/WriteFL.flPageBytes`, written out here so that
this module needs only the page model), read back (U10l of `notes/bbolt-proof-plan.md`): its
header, its count and index (`flCountIdx`), its ids (`flIds`: the sorted ids), and `flCurOK` of a
freelist page at a run no tree page covers and no id of the freelist names.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.FLPageBytes
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- `freelist.Write`'s page (`flPageBytes fl id cnt`, by definition). -/
def flPgB (fl : FLPg) (id : w64) (cnt : Nat) : List w8 :=
  let n := fl.allIds.length
  let body := (if n < 0xFFFF then [] else encode (W64 (n : Int))) ++
    (sortPgids fl.allIds).flatMap encode
  encode (⟨id, W16 (freelistPageFlag : Int), W16 ((if n < 0xFFFF then n else 0xFFFF : Nat) : Int),
      W32 ((cnt - 1 : Nat) : Int)⟩ : Page) ++
    (body ++ List.replicate (cnt * 4096 - 16 - body.length) (W8 0))

theorem fp_flatMap_length (L : List w64) : (L.flatMap (encode : w64 → List w8)).length = 8 * L.length := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, ih, ByteEncoding.encode_length,
      List.length_cons]
    omega

theorem fp_bytesAt_flatMap (L : List w64) (rest : List w8) (i : Nat) (hi : i < L.length) :
    bytesAt (L.flatMap encode ++ rest) (8 * i) 8 = encode (L[i]) := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    have hx : (encode x : List w8).length = 8 := ByteEncoding.encode_length x
    cases i with
    | zero =>
      unfold bytesAt
      simp only [Nat.mul_zero, List.drop_zero, List.flatMap_cons, List.append_assoc,
        List.getElem_cons_zero]
      exact List.take_left' hx
    | succ i =>
      have e : bytesAt ((x :: xs).flatMap encode ++ rest) (8 * (i + 1)) 8 =
          bytesAt (xs.flatMap encode ++ rest) (8 * i) 8 := by
        unfold bytesAt
        rw [List.flatMap_cons, List.append_assoc, show 8 * (i + 1) = 8 + 8 * i by omega,
          ← List.drop_drop, List.drop_left' hx]
      rw [e, ih i (by simp at hi; omega)]
      simp

theorem flPgB_hdr (fl : FLPg) (id : w64) (cnt : Nat) :
    pageHdr (flPgB fl id cnt) = ⟨id, W16 (freelistPageFlag : Int),
      W16 ((if fl.allIds.length < 0xFFFF then fl.allIds.length else 0xFFFF : Nat) : Int),
      W32 ((cnt - 1 : Nat) : Int)⟩ := pageHdr_bytes _ _

theorem flPgB_flags (fl : FLPg) (id : w64) (cnt : Nat) :
    pageFlags (flPgB fl id cnt) = freelistPageFlag := by
  unfold pageFlags; rw [flPgB_hdr]; rfl

theorem flPgB_id (fl : FLPg) (id : w64) (cnt : Nat) : pageId (flPgB fl id cnt) = id.toNat := by
  unfold pageId; rw [flPgB_hdr]

theorem flPgB_overflow (fl : FLPg) (id : w64) (cnt : Nat) (h : cnt - 1 < 2 ^ 32) :
    pageOverflow (flPgB fl id cnt) = cnt - 1 := by
  unfold pageOverflow; rw [flPgB_hdr]
  show (W32 ((cnt - 1 : Nat) : Int)).toNat = cnt - 1
  simp only [W32, BitVec.toNat_ofInt]; omega

theorem flPgB_length (fl : FLPg) (id : w64) (cnt : Nat)
    (h : 8 * (fl.allIds.length + 1) ≤ cnt * 4096 - 16) : (flPgB fl id cnt).length = cnt * 4096 := by
  have hb : ((if fl.allIds.length < 0xFFFF then [] else encode (W64 (fl.allIds.length : Int))) ++
      (sortPgids fl.allIds).flatMap encode).length ≤ 8 * (fl.allIds.length + 1) := by
    have h1 : ((sortPgids fl.allIds).flatMap (encode : w64 → List w8)).length =
        8 * fl.allIds.length := by
      rw [fp_flatMap_length, (sortPgids_perm fl.allIds).length_eq]
    rw [List.length_append, h1]
    split <;> simp [ByteEncoding.encode_length] <;> omega
  unfold flPgB
  simp only [List.length_append, ByteEncoding.encode_length, List.length_replicate] at hb ⊢
  omega

/-- **The page's count and index**: `(n, 0)` below `0xFFFF` ids, else `(n, 1)`. -/
theorem flPgB_countIdx (fl : FLPg) (id : w64) (cnt : Nat) (hn : fl.allIds.length < 2 ^ 63) :
    flCountIdx (flPgB fl id cnt) =
      (fl.allIds.length, if fl.allIds.length < 0xFFFF then 0 else 1) := by
  unfold flCountIdx pageCount
  rw [flPgB_hdr]
  by_cases h : fl.allIds.length < 0xFFFF
  · have e : (W16 ((fl.allIds.length : Nat) : Int)).toNat = fl.allIds.length := by
      simp only [W16, BitVec.toNat_ofInt]; omega
    simp only [h, ite_true, e]
  · have e : (W16 ((65535 : Nat) : Int)).toNat = 65535 := rfl
    simp only [h, ite_false, e, Nat.lt_irrefl]
    congr 1
    unfold flPgB bytesAt
    simp only [h, ite_false, List.append_assoc]
    rw [List.drop_left' (ByteEncoding.encode_length _), List.take_left' (ByteEncoding.encode_length _),
      ByteEncoding.decode_encode]
    simp only [W64, BitVec.toNat_ofInt]; omega

/-- **The page's ids are the freelist's, sorted.** -/
theorem flPgB_ids (fl : FLPg) (id : w64) (cnt : Nat) (hn : fl.allIds.length < 2 ^ 63) :
    flIds (flPgB fl id cnt) = sortPgids fl.allIds := by
  have hlen : (sortPgids fl.allIds).length = fl.allIds.length := (sortPgids_perm _).length_eq
  have key : ∀ i (h2 : i < (sortPgids fl.allIds).length), bytesAt (flPgB fl id cnt)
      (16 + 8 * (if fl.allIds.length < 0xFFFF then 0 else 1) + 8 * i) 8 =
      encode ((sortPgids fl.allIds)[i]'h2) := by
    intro i h2
    unfold flPgB
    by_cases h : fl.allIds.length < 0xFFFF
    · simp only [h, ite_true, List.nil_append, Nat.mul_zero, Nat.add_zero]
      unfold bytesAt
      rw [← List.drop_drop, List.drop_left' (ByteEncoding.encode_length _)]
      exact fp_bytesAt_flatMap _ _ i h2
    · simp only [h, ite_false, List.append_assoc]
      unfold bytesAt
      rw [show 16 + 8 * 1 + 8 * i = 16 + (8 + 8 * i) by omega, ← List.drop_drop,
        List.drop_left' (ByteEncoding.encode_length _), ← List.drop_drop,
        List.drop_left' (ByteEncoding.encode_length _)]
      exact fp_bytesAt_flatMap _ _ i h2
  unfold flIds
  rw [flPgB_countIdx fl id cnt hn]
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [key i h2, ByteEncoding.decode_encode]

theorem fp_W64_toNat (s : Nat) (h : s < 2 ^ 64) : (W64 (s : Int)).toNat = s := by
  simp only [W64, BitVec.toNat_ofInt]; omega

theorem fp_mem_pendingIds (fl : FLPg) (x : w64) :
    x ∈ fl.pendingIds ↔ ∃ t pd, fl.pending !! t = some pd ∧ x ∈ pd.ids := by
  simp only [FLPg.pendingIds, List.mem_flatMap]
  constructor
  · rintro ⟨⟨t, pd⟩, hkv, hx⟩
    exact ⟨t, pd, (GMap.mem_toList _ _ _).1 hkv, hx⟩
  · rintro ⟨t, pd, hp, hx⟩
    exact ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp, hx⟩

/-- **`flCurOK` of a freelist page just written** at the run `[id, id + cnt)`, which no page of
the committed state `C` covers and no id of the freelist names; every pending id is pending for a
committed transaction of `C`, every free id below the mark and covered by no page. -/
theorem flCurOK_flPgB (fl : FLPg) (C : CommitSt) (id : w64) (cnt : Nat)
    (hf : C.flpg = some id.toNat) (h2 : 2 ≤ id.toNat) (hc : 0 < cnt)
    (hend : id.toNat + cnt ≤ C.hwm) (h64 : C.hwm ≤ 2 ^ 64) (hcnt : cnt - 1 < 2 ^ 32)
    (hroom : 8 * (fl.allIds.length + 1) ≤ cnt * 4096 - 16) (hwf : fl.WF)
    (hrun : ∀ s, id.toNat ≤ s → s < id.toNat + cnt →
      ¬ coversSlot C.pages s ∧ ∀ x ∈ fl.allIds, x.toNat ≠ s)
    (hpend : ∀ t pd, fl.pending !! t = some pd → t.toNat ≤ C.txid)
    (hfree : ∀ x ∈ fl.free, x.toNat < C.hwm ∧ x.toNat < 2 ^ 62 ∧ ¬ coversSlot C.pages x.toNat)
    (hal : ∀ a, fl.allocs !! id = some a → a.toNat ≤ C.txid) :
    flCurOK fl C (flPgB fl id cnt) := by
  intro f hf'
  rw [hf] at hf'
  cases hf'
  have hn : fl.allIds.length < 2 ^ 63 := hwf.2.2.2.1
  have hov := flPgB_overflow fl id cnt hcnt
  have hlen := flPgB_length fl id cnt hroom
  have hids := flPgB_ids fl id cnt hn
  have hmem : ∀ x, x ∈ flIds (flPgB fl id cnt) ↔ x ∈ fl.allIds := fun x => by
    rw [hids]; exact (sortPgids_perm _).mem_iff
  have h1 : 1 + pageOverflow (flPgB fl id cnt) = cnt := by omega
  rw [h1]
  refine ⟨h2, hend, hlen, flPgB_flags fl id cnt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    flPgB_id fl id cnt⟩
  · rw [flPgB_countIdx fl id cnt hn, hlen]
    split <;> omega
  · rw [hids]; exact (sortPgids_perm _).nodup_iff.2 hwf.1
  · intro x hx; exact hwf.2.1 x ((hmem x).1 hx)
  · rintro x hx ⟨a, b⟩
    exact (hrun x.toNat a b).2 x ((hmem x).1 hx) rfl
  · intro s a b
    refine ⟨(hrun s a b).1, fun hm => ?_⟩
    have := (hrun s a b).2 _ hm
    rw [fp_W64_toNat s (by omega)] at this
    exact this rfl
  · intro x hx; exact (hmem x).2 (List.mem_append_left _ hx)
  · rintro x ⟨t, pd, hp, hx, -⟩
    exact (hmem x).2 (List.mem_append_right _ ((fp_mem_pendingIds fl x).2 ⟨t, pd, hp, hx⟩))
  · intro x hx
    rcases List.mem_append.1 ((hmem x).1 hx) with h | h
    · exact Or.inr (hfree x h)
    · obtain ⟨t, pd, hp, hx'⟩ := (fp_mem_pendingIds fl x).1 h
      exact Or.inl ⟨t, pd, hp, hx', hpend t pd hp⟩
  · intro a ha
    rw [show W64 ((id.toNat : Nat) : Int) = id by simp [W64]] at ha
    exact hal a ha

end pure

end bbolt
end EtcdGrove
end Perennial
