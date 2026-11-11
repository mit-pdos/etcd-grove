/-
`Open`'s pure facts (U11g): the file's facts after its branch (a decoded file, or the image
`init` wrote), and what they give `mmapUnlocked` and `loadFreelist` (`lfOK`).
-/
module

public import Proof.go_etcd_io.bbolt.DB__loadFreelist
public import Proof.go_etcd_io.bbolt.Open.InitImage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

section pure
variable [GooseExts]

/-- **The opened file's facts** (`fileHolds_decode`'s, or `initImg_ok`'s): the file's bytes `xs`
(`OsMeta` `m`) are an image of `C`, which holds `D`. -/
def openOK (C : CommitSt) (D : Data) (m : OsMeta) (xs : List (w8 × Bool)) : Prop :=
  fileImage (xs.map Prod.fst) C ∧ C.metaOk ∧ treeOK C ∧ flFileOK (xs.map Prod.fst) C ∧
    C.hwm * 4096 ≤ m.size ∧ 1 ≤ C.txid ∧ C.txid < 2 ^ 62 ∧ treeData C = D

theorem openOK_init (m : OsMeta) (xs : List (w8 × Bool)) (hx : xs.map Prod.fst = initImg)
    (hl : xs.length = m.size) : openOK initC ∅ m xs := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := initImg_ok
  have hl' : initImg.length = m.size := by rw [← hx, List.length_map, hl]
  unfold openOK
  rw [hx]
  exact ⟨h1, h2, h3, h4, hl' ▸ h5, h6, h7, h8⟩

theorem treeOK_root_open (C : CommitSt) (htree : treeOK C) : 2 ≤ C.root ∧ C.root < C.hwm := by
  obtain ⟨⟨hwf, -⟩, -⟩ := htree
  cases hwf with
  | page _ _ h2 hlt _ _ _ _ => exact ⟨h2, hlt⟩

theorem openOK_size (C : CommitSt) (D : Data) (m : OsMeta) (xs : List (w8 × Bool))
    (h : openOK C D m xs) : 12288 ≤ m.size := by
  have h1 := treeOK_root_open C h.2.2.1
  have h2 := h.2.2.2.2.1
  have : 3 * 4096 ≤ C.hwm * 4096 := Nat.mul_le_mul_right _ (by omega)
  omega

/-- A valid meta in one of the two first slots (`mmapUnlocked.spec_own`'s premise). -/
theorem openOK_meta (C : CommitSt) (D : Data) (m : OsMeta) (xs : List (w8 × Bool))
    (h : openOK C D m xs) :
    metaValid (metaOf (bytesAt (xs.map Prod.fst) 0 4096)) ∨
      metaValid (metaOf (bytesAt (xs.map Prod.fst) 4096 4096)) := by
  obtain ⟨⟨h0, h1, -⟩, hmo, -⟩ := h
  have hv := hmo.2.2.2.2.2.1
  unfold CommitSt.slot at hv
  split at hv
  · left; rw [← h0]; exact hv
  · right; rw [← h1]; exact hv

/-- **`loadFreelist`'s facts** at `Open`, from the opened file's and the mapping's. -/
theorem openOK_lfOK (N : Namespace) (db : Loc) (C : CommitSt) (D : Data) (m : OsMeta)
    (xs : List (w8 × Bool)) (b : Loc) (L : Nat) (h : openOK C D m xs) (hl : xs.length = m.size)
    (hsz : m.size < 2 ^ 62) (hL : m.size ≤ L) (hN : (↑N : CoPset) ## ↑osN) (hdb : db ≠ null) :
    lfOK N db C b L { m with maps := GMap.singleton b L } xs := by
  have h12 := openOK_size C D m xs h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  exact ⟨h1, h2, h3, h4, by omega, by omega, hl, hL, by simp only; omega, rfl, h6, h7, hN, hdb⟩

end pure

end bbolt
end EtcdGrove
end Perennial
