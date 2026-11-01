/-
The meta pages `init` lays out (`initBytes`, `Pages.lean`), read back: both metas valid, the
current one (`curMeta`) meta 1, with root 3 and high water mark 4 (`metaPagesOk`), and the empty
root page holds no value. For `Open`'s proof, which builds an open database over them.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.mit_pdos.etcd_grove.examples.bboltfs

section pure
variable [GooseExts]

theorem pageMeta_encode (h : Page) (v : Meta) (rest : List w8) :
    pageMeta (encode h ++ encode v ++ rest) = v := by
  unfold pageMeta
  rw [List.append_assoc, List.drop_left' (ByteEncoding.encode_length h),
    List.take_left' (ByteEncoding.encode_length v), ByteEncoding.decode_encode]

theorem pageHdrOf_encode (h : Page) (rest : List w8) : pageHdrOf (encode h ++ rest) = h := by
  unfold pageHdrOf
  rw [List.take_left' (ByteEncoding.encode_length h), ByteEncoding.decode_encode]

theorem initBytes_meta0 : fileMeta initBytes 0 = initMeta 0 := by
  unfold fileMeta initBytes metaPageBytes
  simp only [Nat.mul_zero, List.drop_zero, List.append_assoc]
  rw [← List.append_assoc, pageMeta_encode]

theorem initBytes_meta1 : fileMeta initBytes 1 = initMeta 1 := by
  unfold fileMeta initBytes
  rw [List.append_assoc, List.append_assoc,
    List.drop_left' (by rw [metaPageBytes_length]), metaPageBytes, List.append_assoc,
    List.append_assoc, ← List.append_assoc, pageMeta_encode]

/-- A meta depends only on the bytes up to its end. -/
theorem fileMeta_take (xs : List w8) (n i : Nat) (h : 4096 * i + 80 ≤ n) :
    fileMeta (xs.take n) i = fileMeta xs i := by
  unfold fileMeta; rw [List.drop_take]; exact pageMeta_take _ _ (by omega)

/-- The meta pages of a file whose first two pages are `initBytes`'s. -/
theorem initMetas (mp : List w8) (h : mp.take 8192 = initBytes.take 8192) (i : Nat) (hi : i < 2) :
    fileMeta mp i = initMeta i := by
  rw [← fileMeta_take mp 8192 i (by omega), h, fileMeta_take _ _ _ (by omega)]
  rcases i with _ | _ | i
  · exact initBytes_meta0
  · exact initBytes_meta1
  · omega

theorem initMeta_txid (i : Nat) : (initMeta i).txid' = W64 (i : Int) := rfl
theorem initMeta_root (i : Nat) : (initMeta i).root'.root' = W64 3 := rfl
theorem initMeta_pgid (i : Nat) : (initMeta i).pgid' = W64 4 := rfl

theorem curMeta_init (mp : List w8) (h : mp.take 8192 = initBytes.take 8192) :
    curMeta mp = initMeta 1 := by
  unfold curMeta
  dsimp only
  rw [initMetas mp h 0 (by omega), initMetas mp h 1 (by omega), initMeta_txid, initMeta_txid,
    if_pos (by decide), if_pos (initMeta_valid 1)]

theorem metaPagesOk_init (mp : List w8) (h : mp.take 8192 = initBytes.take 8192)
    (hl : mp.length = 8192) : metaPagesOk mp := by
  have hc := curMeta_init mp h
  refine ⟨hl, Or.inl (by rw [initMetas mp h 0 (by omega)]; exact initMeta_valid 0), ?_, ?_, ?_⟩ <;>
    simp only [curRoot, curPgid, hc, initMeta_root, initMeta_pgid] <;> decide

/-- `init`'s root page (page 3): empty, it holds no value. -/
theorem initRoot_val : pageVal (emptyPageBytes (W64 3) (W16 2)) = none := by
  unfold pageVal emptyPageBytes
  rw [pageHdrOf_encode, if_neg (by unfold pageHdr; simp)]

end pure

end github_com.mit_pdos.etcd_grove.examples.bboltfs

end Perennial
