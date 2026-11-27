/-
**A well-formed file that `needsInit` accepts holds no data** (`Open`'s `init` branch, the fork's
crash-safe `init`, `issues/bbolt-init-not-crash-safe.md`): a file `fileOK` describes, of at most four
pages whose every byte is zero or `initImg`'s (`initPartial`), has an empty root leaf, so
initializing it again loses nothing. Its root page is page 2 or 3 (`treeOK`: `2 ≤ root < hwm`, and
`hwm` pages fit in the file), whose count bytes (offsets 10 and 11 of the page) `initImg` writes
as zero.
-/
module

public import Proof.go_etcd_io.bbolt.Open.Facts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt.internal.common Spill

section pure
variable [GooseExts]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk]
set_option linter.unusedSectionVars false

/-- A page's element count is its bytes 10 and 11 (the header's `count`). -/
theorem pageCount_bytes (pg : List w8) :
    pageCount pg = (decode (bytesAt pg 10 2) : w16).toNat := by
  have e : (((bytesAt pg 0 16).drop 8).drop 2).take 2 = bytesAt pg 10 2 := by
    unfold bytesAt
    rw [List.drop_zero, List.drop_drop, List.drop_take, List.take_take]
    try rfl
  show (decode ((((bytesAt pg 0 16).drop 8).drop 2).take 2) : w16).toNat = _
  rw [e]

omit [GooseExts] in
/-- Two bytes of a list, read at an offset. -/
theorem initPartial_bytesAt_two (X : List w8) (a : Nat) (b0 b1 : w8) (h0 : X[a]? = some b0)
    (h1 : X[a + 1]? = some b1) : bytesAt X a 2 = [b0, b1] := by
  obtain ⟨ha, e0⟩ := List.getElem?_eq_some_iff.1 h0
  obtain ⟨ha1, e1⟩ := List.getElem?_eq_some_iff.1 h1
  unfold bytesAt
  rw [List.drop_eq_getElem_cons ha, List.drop_eq_getElem_cons ha1, e0, e1]
  try rfl

/-- The count bytes of an encoded page header. -/
theorem encode_page_count (h : Page) : ((encode h).drop 10).take 2 = encode h.count' := by
  show ((encode h.id' ++ (encode h.flags' ++ (encode h.count' ++ encode h.overflow'))).drop 10).take 2
    = _
  have e : 10 = (encode h.id' ++ encode h.flags').length := by simp
  rw [e, ← List.append_assoc, List.drop_left, List.take_left' (ByteEncoding.encode_length _)]

theorem encode_w16_zero : encode (W16 0 : w16) = [W8 0, W8 0] := by
  rw [encode_w16, show (W16 0 : w16).toNat = 0 from rfl]
  rfl

/-- `initImg`'s count bytes of pages 2 and 3 are zero. -/
theorem initImg_count_bytes (r : Nat) (hr : r = 2 ∨ r = 3) :
    bytesAt initImg (4096 * r + 10) 2 = [W8 0, W8 0] := by
  have hs : bytesAt initImg (4096 * r + 10) 2 = bytesAt (bytesAt initImg (4096 * r) 4096) 10 2 := by
    unfold bytesAt
    rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]
  have he : ∀ (id : Nat) (fl : w16), bytesAt (emptyPg id fl) 10 2 = [W8 0, W8 0] := by
    intro id fl
    unfold bytesAt emptyPg
    rw [List.drop_append_of_le_length (by rw [ByteEncoding.encode_length]; omega),
      List.take_append_of_le_length (by simp), encode_page_count]
    exact encode_w16_zero
  rcases hr with rfl | rfl
  · rw [hs, initImg_slot 2 (by omega)]; exact he 2 (W16 16)
  · rw [hs, initImg_slot 3 (by omega)]; exact he 3 (W16 2)

theorem initImg_count_zero (r j : Nat) (hr : r = 2 ∨ r = 3) (hj : j < 2) :
    initImg[4096 * r + 10 + j]? = some (W8 0) := by
  have := congrArg (fun l : List w8 => l[j]?) (initImg_count_bytes r hr)
  simp only [bytesAt, List.getElem?_take, List.getElem?_drop, hj, ↓reduceIte] at this
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simpa using this

/-- **The root of a `fileOK` image whose bytes `initPartial` accepts is empty**: its count is
zero. -/
theorem initPartial_root_count (X : List w8) (C : CommitSt) (hI : fileImage X C)
    (htree : treeOK C) (hsz : C.hwm * 4096 ≤ X.length) (hp : initPartial X) (pg : List w8)
    (hpg : C.pages !! C.root = some pg) : pageCount pg = 0 := by
  obtain ⟨hr2, hrh⟩ := treeOK_root_open C htree
  have hl := hp.1
  have hrt : C.root = 2 ∨ C.root = 3 := by omega
  have hr16 : 4096 * C.root + 16 ≤ X.length := by omega
  -- the page is the file's page at the root
  have hfp : filePages X C.hwm !! C.root = some (filePage X C.root) := by
    unfold filePages
    exact ofList_map_lookup_mem (filePage X) _ C.root (List.mem_range.2 hrh)
  have hpg' : pg = filePage X C.root := by
    rw [hI.2.2, treePages_lookup] at hpg
    split at hpg
    · rw [hfp] at hpg; exact (Option.some.inj hpg).symm
    · cases hpg
  subst hpg'
  -- its count bytes
  have hz : ∀ j, j < 2 → X[4096 * C.root + 10 + j]? = some (W8 0) := by
    intro j hj
    obtain ⟨b, hb⟩ : ∃ b, X[4096 * C.root + 10 + j]? = some b :=
      ⟨X[4096 * C.root + 10 + j]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    rcases hp.2 _ b hb with h | h
    · rw [hb, h]
    · rw [initImg_count_zero C.root j hrt hj] at h
      rw [hb, Option.some.inj h]
  have hc : bytesAt (filePage X C.root) 10 2 = bytesAt X (4096 * C.root + 10) 2 := by
    unfold filePage bytesAt
    rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]
  rw [pageCount_bytes, hc,
    initPartial_bytesAt_two X _ (W8 0) (W8 0) (hz 0 (by omega)) (hz 1 (by omega))]
  rfl

/-- **`Open`'s `init` branch on a well-formed file loses nothing**: an opened file's facts
(`openOK`, `fileOK`'s) of bytes `initPartial` accepts hold no data. -/
theorem openOK_initPartial (C : CommitSt) (D : Data) (m : Fs.OsMeta) (xs : List Fs.ByteG)
    (h : openOK C D m xs) (hl : xs.length = m.size) (hp : initPartial (xs.map Prod.fst)) :
    D = ∅ := by
  obtain ⟨hI, -, htree, -, hsz, -, -, hD⟩ := h
  have hsz' : C.hwm * 4096 ≤ (xs.map Prod.fst).length := by rw [List.length_map]; omega
  have hcount := initPartial_root_count _ C hI htree hsz' hp
  have hE : treeEntries C.pages C.root = [] := by
    unfold treeEntries treeLeaves
    generalize C.pages.size = n
    cases hlk : C.pages !! C.root with
    | none => simp only [leavesF, hlk, List.flatMap_nil]
    | some pg =>
      have hc := hcount pg hlk
      by_cases hf : pageFlags pg = leafPageFlag
      · simp only [leavesF, hlk, hf, ↓reduceIte, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, leafEnts, hc, List.range_zero, List.map_nil]
      · simp only [leavesF, hlk, hf, ↓reduceIte, hc, List.range_zero, List.flatMap_nil]
  rw [← hD]
  unfold treeData
  rw [hE]
  try rfl

end pure

end bbolt
end EtcdGrove
end Perennial
