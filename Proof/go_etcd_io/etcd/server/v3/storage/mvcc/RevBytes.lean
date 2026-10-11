/-
The revision encoding (`revision.go`): a bucket key is `main` big-endian, a `'_'` and `sub`
big-endian (17 bytes), and a tombstone's has a trailing `'t'` (18 bytes). Lean-first. The
big-endian encoding `u64Be` is the consistent index's (`etcdserver/InvCindex.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-- The separator `'_'` at byte 8. -/
abbrev revSep : w8 := W8 95
/-- The tombstone mark `'t'` at byte 17. -/
abbrev markTomb : w8 := W8 116

/-- A tombstone's key: the revision's 17 bytes and the mark. -/
theorem revBytes_true (r : Rev) : revBytes r true = revBytes r false ++ [markTomb] := by
  simp [revBytes, markTomb]

/-- A bucket key's bytes into a buffer of 17 or 18 bytes whose tail after byte 17 is `rest`:
the mark for a tombstone, else the tail as it was (`BucketKeyToBytes`). -/
def bucketKeyBytes (r : Rev) (tomb : Bool) (rest : List w8) : List w8 :=
  revBytes r false ++ (if tomb then [markTomb] else rest)

theorem bucketKeyBytes_true (r : Rev) (rest : List w8) :
    bucketKeyBytes r true rest = revBytes r true := by
  simp [bucketKeyBytes, revBytes_true]

/-- What `isTombstone` decides: 18 bytes, the last the mark. -/
def isTomb (bs : List w8) : Bool := decide (bs.length = 18 ∧ bs[17]? = some markTomb)

theorem revBytes_false_length (r : Rev) : (revBytes r false).length = 17 := by
  simp [revBytes_length]

theorem revBytes_take8 (r : Rev) : (revBytes r false).take 8 = u64Be r.main := by
  simp only [revBytes, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.append_assoc]
  rw [List.take_append_of_le_length (by simp [u64Be_length]),
    List.take_of_length_le (by simp [u64Be_length])]

theorem revBytes_getElem8 (r : Rev) : (revBytes r false)[8]? = some revSep := by
  simp only [revBytes, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.append_assoc]
  rw [List.getElem?_append_right (by simp [u64Be_length])]; simp [u64Be_length, revSep]

theorem revBytes_drop9 (r : Rev) : (revBytes r false).drop 9 = u64Be r.sub := by
  simp only [revBytes, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.append_assoc]
  rw [List.drop_append, List.drop_of_length_le (by simp [u64Be_length])]
  simp [u64Be_length]

theorem isTomb_of_length_ne (bs : List w8) (h : bs.length ≠ 18) : isTomb bs = false := by
  simp [isTomb, h]

theorem isTomb_of_getElem (bs : List w8) (v : w8) (h : bs.length = 18) (hv : bs[17]? = some v) :
    isTomb bs = decide (v = markTomb) := by
  simp only [isTomb, h, hv, Option.some.injEq, true_and]

/-- Decoding: the tail after the 17 bytes of a revision. -/
theorem isTomb_revBytes (r : Rev) (rest : List w8) :
    isTomb (revBytes r false ++ rest) = decide (rest = [markTomb]) := by
  unfold isTomb
  rw [List.getElem?_append_right (by simp [revBytes_false_length])]
  simp only [List.length_append, revBytes_false_length]
  cases rest with
  | nil => simp
  | cons c t =>
    cases t with
    | nil => simp
    | cons d u => simp; intro h; omega


/-! ## The encoder's steps (`BucketKeyToBytes`) -/

/-- The buffer after `PutUint64(bytes, main)` and `bytes[8] = '_'`. -/
theorem enc_step1 (m : w64) (bs : List w8) (h : 9 ≤ bs.length) :
    (u64Be m ++ bs.drop 8).set 8 revSep = u64Be m ++ revSep :: bs.drop 9 := by
  rw [List.set_append_right _ _ (by simp [u64Be_length]), u64Be_length, Nat.sub_self,
    List.drop_eq_getElem_cons (show 8 < bs.length by omega), List.set_cons_zero]

theorem enc_length (m : w64) (l : List w8) : (u64Be m ++ revSep :: l).length = 9 + l.length := by
  simp [u64Be_length]; omega

theorem enc_take9 (m : w64) (l : List w8) :
    (u64Be m ++ revSep :: l).take 9 = u64Be m ++ [revSep] := by
  rw [List.take_append, List.take_of_length_le (by simp [u64Be_length]),
    u64Be_length]
  simp

theorem enc_subslice9 (m : w64) (l : List w8) :
    subslice 9 (9 + l.length) (u64Be m ++ revSep :: l) = l := by
  unfold subslice
  rw [← enc_length m l, List.take_length, show 9 = 8 + 1 from rfl, ← List.drop_drop,
    List.drop_left' (u64Be_length m)]
  simp

theorem enc_drop_length (m : w64) (l : List w8) :
    (u64Be m ++ revSep :: l).drop (9 + l.length) = [] := by
  rw [← enc_length m l, List.drop_length]

/-- The 17 bytes, split as the encoder leaves them: before 9, from 9, after the end. -/
theorem revBytes_eq (r : Rev) (rest : List w8) :
    revBytes r false ++ rest = u64Be r.main ++ revSep :: (u64Be r.sub ++ rest) := by
  simp [revBytes, revSep]

section go
variable [ext : FfiSyntax]

/-- The same, of a Go `Revision` value. -/
theorem revBytes_revOf_eq (v : go_etcd_io.etcd.server.v3.storage.mvcc.Revision) (rest : List w8) :
    revBytes (revOf v) false ++ rest = u64Be v.Main' ++ revSep :: (u64Be v.Sub' ++ rest) := by
  simp [revBytes, revSep]

end go

theorem bucketKeyBytes_false (r : Rev) (rest : List w8) :
    bucketKeyBytes r false rest = revBytes r false ++ rest := by
  simp [bucketKeyBytes]

/-- Setting the 18th byte of a tombstone's 18-byte buffer. -/
theorem bucketKeyBytes_set17 (r : Rev) (c : w8) :
    (revBytes r false ++ [c]).set 17 markTomb = bucketKeyBytes r true [c] := by
  rw [List.set_append_right _ _ (by simp [revBytes_false_length]), revBytes_false_length]
  simp [bucketKeyBytes]


/-! ## The decoder's steps (`BytesToBucketKey`) -/

theorem revBytes_rest_length (r : Rev) (rest : List w8) :
    (revBytes r false ++ rest).length = 17 + rest.length := by
  simp [revBytes_false_length]

theorem revBytes_rest_getElem8 (r : Rev) (rest : List w8) :
    (revBytes r false ++ rest)[8]? = some revSep := by
  rw [List.getElem?_append_left (by simp [revBytes_false_length]), revBytes_getElem8]

/-- `bytes[0:8]` holds the main revision. -/
theorem revBytes_rest_subslice8 (r : Rev) (rest : List w8) :
    subslice 0 8 (revBytes r false ++ rest) = u64Be r.main := by
  unfold subslice
  rw [List.drop_zero, List.take_append_of_le_length (by simp [revBytes_false_length]),
    revBytes_take8]

theorem revBytes_rest_join8 (r : Rev) (rest : List w8) :
    u64Be r.main ++ (revBytes r false ++ rest).drop 8 = revBytes r false ++ rest := by
  conv => rhs; rw [← List.take_append_drop 8 (revBytes r false ++ rest)]
  rw [List.take_append_of_le_length (by simp [revBytes_false_length]), revBytes_take8]

/-- `bytes[9:]` holds the sub revision and the tail. -/
theorem revBytes_rest_subslice9 (r : Rev) (rest : List w8) :
    subslice 9 (revBytes r false ++ rest).length (revBytes r false ++ rest) =
      u64Be r.sub ++ rest := by
  unfold subslice
  rw [List.take_length, List.drop_append_of_le_length (by simp [revBytes_false_length]),
    revBytes_drop9]

theorem revBytes_rest_join9 (r : Rev) (rest : List w8) :
    (revBytes r false ++ rest).take 9 ++ (u64Be r.sub ++ rest) = revBytes r false ++ rest := by
  conv => rhs; rw [← List.take_append_drop 9 (revBytes r false ++ rest)]
  rw [List.drop_append_of_le_length (by simp [revBytes_false_length]), revBytes_drop9]

end mvcc
end EtcdGrove
end Perennial
