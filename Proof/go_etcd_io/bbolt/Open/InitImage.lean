/-
The image `DB.init` writes (U11f of `notes/bbolt-proof-plan.md`): two meta pages (`metaBuf` of
`initMv 0` and `initMv 1`: txid `i` at slot `i`, root page 3, freelist page 2, high-water mark 4),
an empty freelist page 2 and an empty leaf page 3 (`initImg`), and its committed state `initC`
(txid 1), with `fileOK`'s facts of it (`initImg_ok`).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.MetaBuf
public import Proof.go_etcd_io.bbolt.Inv.FileHolds
public import Proof.go_etcd_io.bbolt.Spill.STree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt.internal.common Spill

section image
variable [GooseExts]

/-- The meta `init` writes at slot `i` (before its checksum). -/
def initMv (i : Nat) : Meta :=
  ⟨W32 0xED0CDAED, W32 2, W32 4096, W32 0, ⟨W64 3, W64 0⟩, W64 2, W64 4, W64 (i : Int), W64 0⟩

/-- The header of an empty page `id` with flags `fl`. -/
def emptyHdr (id : Nat) (fl : w16) : Page := ⟨W64 (id : Int), fl, W16 0, W32 0⟩

/-- An empty page `id` with flags `fl` (a zeroed page with its header set). -/
def emptyPg (id : Nat) (fl : w16) : List w8 := encode (emptyHdr id fl) ++ List.replicate 4080 (W8 0)

/-- **The four pages `init` writes.** -/
def initImg : List w8 :=
  metaBuf (initMv 0) ++ metaBuf (initMv 1) ++ emptyPg 2 (W16 16) ++ emptyPg 3 (W16 2)

/-- **The committed state of `initImg`.** -/
def initC : CommitSt :=
  { m0 := metaBuf (initMv 0), m1 := metaBuf (initMv 1),
    pages := treePages (filePages initImg 4) 3, root := 3, hwm := 4, txid := 1, flpg := some 2 }

theorem emptyPg_length (id : Nat) (fl : w16) : (emptyPg id fl).length = 4096 := by
  simp only [emptyPg, List.length_append, ByteEncoding.encode_length, List.length_replicate]

theorem initImg_length : initImg.length = 16384 := by
  simp only [initImg, List.length_append, metaBuf_length, emptyPg_length]

/-- The header of a page laid out as a header's encoding and bytes after it. -/
private theorem pageHdr_encode (h : Page) (r : List w8) : pageHdr (encode h ++ r) = h := by
  unfold pageHdr bytesAt
  rw [List.drop_zero, List.take_left' (ByteEncoding.encode_length _), ByteEncoding.decode_encode]

theorem metaBuf_hdr' (mv : Meta) : pageHdr (metaBuf mv) = metaHdr mv := by
  unfold metaBuf; rw [List.append_assoc, pageHdr_encode]

theorem emptyPg_hdr (id : Nat) (fl : w16) : pageHdr (emptyPg id fl) = emptyHdr id fl :=
  pageHdr_encode _ _

/-- The four slots of the image. -/
theorem initImg_slot (k : Nat) (hk : k < 4) :
    bytesAt initImg (4096 * k) 4096 =
      [metaBuf (initMv 0), metaBuf (initMv 1), emptyPg 2 (W16 16), emptyPg 3 (W16 2)][k]'(by
        simp; omega) := by
  have h0 := metaBuf_length (initMv 0)
  have h1 := metaBuf_length (initMv 1)
  have h2 := emptyPg_length 2 (W16 16)
  have h3 := emptyPg_length 3 (W16 2)
  unfold bytesAt initImg
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · simp only [List.append_assoc, Nat.mul_zero, List.drop_zero]
    rw [List.take_left' h0]; rfl
  · simp only [List.append_assoc, Nat.mul_one]
    rw [List.drop_left' h0, List.take_left' h1]; rfl
  · rw [show 4096 * 2 = (metaBuf (initMv 0) ++ metaBuf (initMv 1)).length by simp [h0, h1]]
    simp only [List.append_assoc]
    rw [← List.append_assoc (metaBuf (initMv 0)), List.drop_left, List.take_left' h2]; rfl
  · rw [show 4096 * 3 = (metaBuf (initMv 0) ++ metaBuf (initMv 1) ++ emptyPg 2 (W16 16)).length by
      simp only [List.length_append, h0, h1, h2]]
    rw [List.drop_left, List.take_of_length_le (by omega)]; rfl

/-- The image's pages are one slot each. -/
theorem initImg_filePage (k : Nat) (hk : k < 4) :
    filePage initImg k = bytesAt initImg (4096 * k) 4096 := by
  unfold filePage
  have ho : pageOverflow (bytesAt initImg (4096 * k) 4096) = 0 := by
    rw [initImg_slot k hk]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, pageOverflow, metaBuf_hdr',
        emptyPg_hdr] <;> rfl
  rw [ho]

theorem initImg_page3 : filePage initImg 3 = emptyPg 3 (W16 2) := by
  rw [initImg_filePage 3 (by omega), initImg_slot 3 (by omega)]; rfl

theorem initImg_page2 : filePage initImg 2 = emptyPg 2 (W16 16) := by
  rw [initImg_filePage 2 (by omega), initImg_slot 2 (by omega)]; rfl

theorem emptyPg_flags (id : Nat) (fl : w16) : pageFlags (emptyPg id fl) = fl.toNat := by
  unfold pageFlags; rw [emptyPg_hdr]; rfl

theorem emptyPg_count (id : Nat) (fl : w16) : pageCount (emptyPg id fl) = 0 := by
  unfold pageCount; rw [emptyPg_hdr]; rfl

theorem emptyPg_overflow (id : Nat) (fl : w16) : pageOverflow (emptyPg id fl) = 0 := by
  unfold pageOverflow; rw [emptyPg_hdr]; rfl

theorem emptyPg_id (id : Nat) (fl : w16) (h : id < 2 ^ 64) : pageId (emptyPg id fl) = id := by
  unfold pageId; rw [emptyPg_hdr]; simp [emptyHdr]; omega

omit [GooseExts] in
/-- A lookup in a map built from a list of keys, of a key of the list. -/
theorem ofList_map_lookup_mem {V : Type} (f : Nat → V) :
    ∀ (l : List Nat) (id : Nat), id ∈ l →
      (GMap.ofList (l.map fun i => (i, f i))) !! id = some (f id)
  | [], id, h => by cases h
  | a :: l, id, h => by
    simp only [List.map_cons, GMap.ofList]
    by_cases ha : a = id
    · subst ha; rw [GMap.lookup_insert]
    · rw [GMap.lookup_insert_ne _ _ ha]
      exact ofList_map_lookup_mem f l id (by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm ha
        · exact h)

/-- The tree of an empty leaf is its root page alone. -/
theorem treeHas_emptyLeaf (P : Pages) (r : Nat) (pg : List w8) (hp : P !! r = some pg)
    (hfl : pageFlags pg = leafPageFlag) (hc : pageCount pg = 0) (id : Nat)
    (h : treeHas P r id) : id = r := by
  cases h with
  | root => rfl
  | sub _ pg' _ hp' hpg =>
    rw [hp] at hp'; cases hp'
    cases hpg with
    | child _ i _ hb hi _ => rw [hfl] at hb; cases hb
    | bucket _ i _ _ hi _ _ => omega

theorem initFile_lookup3 : filePages initImg 4 !! 3 = some (emptyPg 3 (W16 2)) := by
  unfold filePages
  rw [ofList_map_lookup_mem (filePage initImg) _ 3 (by simp), initImg_page3]

/-- **The tree of `initC`**: page 3, an empty leaf. -/
theorem initC_lookup (id : Nat) (pg : List w8) :
    initC.pages !! id = some pg ↔ id = 3 ∧ pg = emptyPg 3 (W16 2) := by
  have hl : pageFlags (emptyPg 3 (W16 2)) = leafPageFlag := by rw [emptyPg_flags]; rfl
  show treePages (filePages initImg 4) 3 !! id = some pg ↔ _
  rw [treePages_lookup]
  constructor
  · intro h
    split at h
    · rename_i hh
      have := treeHas_emptyLeaf _ 3 _ initFile_lookup3 hl (emptyPg_count _ _) id hh
      subst this
      rw [initFile_lookup3] at h; cases h
      exact ⟨rfl, rfl⟩
    · cases h
  · rintro ⟨rfl, rfl⟩
    simp only [treeHas.root 3 _ initFile_lookup3, ↓reduceIte, initFile_lookup3]

theorem initC_lookup3 : initC.pages !! 3 = some (emptyPg 3 (W16 2)) :=
  (initC_lookup 3 _).2 ⟨rfl, rfl⟩

theorem initC_treeHas (id : Nat) (h : treeHas initC.pages 3 id) : id = 3 :=
  treeHas_emptyLeaf _ 3 _ initC_lookup3 (by rw [emptyPg_flags]; rfl) (emptyPg_count _ _) id h

theorem initC_coversSlot (s : Nat) (h : coversSlot initC.pages s) : s = 3 := by
  obtain ⟨id, pg, hp, h1, h2⟩ := h
  obtain ⟨rfl, rfl⟩ := (initC_lookup id pg).1 hp
  rw [emptyPg_overflow] at h2; omega

/-! ## `fileOK`'s facts -/

theorem initC_fileImage : fileImage initImg initC := by
  refine ⟨?_, ?_, rfl⟩
  · rw [show (0 : Nat) = 4096 * 0 from rfl, initImg_slot 0 (by omega)]; rfl
  · rw [show (4096 : Nat) = 4096 * 1 from rfl, initImg_slot 1 (by omega)]; rfl

theorem initMv_summed_pageSize (i : Nat) : (metaSummed (initMv i)).pageSize'.toNat = 4096 := rfl

theorem initMv_valid (i : Nat) : metaValid (metaSummed (initMv i)) :=
  metaValid_metaSummed _ rfl rfl

theorem initC_metaOk : initC.metaOk := by
  have hs : ∀ i, initC.slot i = metaBuf (initMv (i % 2)) := by
    intro i; unfold CommitSt.slot initC
    rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]
  refine ⟨metaBuf_length _, metaBuf_length _, ?_, (metaBuf_probes _).1, (metaBuf_probes _).2,
    ?_, ?_, ?_⟩
  · intro i _; rw [hs, metaOf_metaBuf]; rfl
  · rw [hs, metaOf_metaBuf]; exact initMv_valid _
  · rw [hs, metaOf_metaBuf]
    refine ⟨rfl, rfl, rfl, ?_⟩
    unfold metaFlpg; simp [initMv, metaSummed, pgidNoFreelist, initC]
  · intro _; rw [hs, metaOf_metaBuf]; show (W64 ((((1 : Nat) + 1) % 2 : Nat) : Int)).toNat < 1
    decide

theorem initC_treeOK : treeOK initC := by
  have hl : pageFlags (emptyPg 3 (W16 2)) = leafPageFlag := by rw [emptyPg_flags]; rfl
  have hb : ¬ pageFlags (emptyPg 3 (W16 2)) = branchPageFlag := by rw [emptyPg_flags]; decide
  have hc := emptyPg_count 3 (W16 2)
  have hlen := emptyPg_length 3 (W16 2)
  refine ⟨⟨?_, ⟨?_, ?_, ?_⟩, ?_, ⟨fun _ => 0, ?_⟩⟩, treePages_idem _ _, ?_, ?_, ?_, by
    show 1 < 2 ^ 63; omega⟩
  · -- treeWF
    refine treeWF.page 3 _ (by omega) (by show 3 < 4; omega) initC_lookup3
      (emptyPg_id _ _ (by omega)) (by rw [emptyPg_overflow, hlen]) ?_
    refine pageTreeWF.leaf _ _ hl ⟨Nat.le_refl _, ?_, ?_, ?_⟩ ?_
    · rw [hc, hlen]; decide
    · intro i hi; omega
    · intro i j _ hj; omega
    · intro i hi; omega
  · intro id pg hp
    obtain ⟨rfl, rfl⟩ := (initC_lookup id pg).1 hp
    exact ⟨fun _ i hi => by omega, fun h => absurd h hb⟩
  · intro id pg hp hfb
    obtain ⟨rfl, rfl⟩ := (initC_lookup id pg).1 hp
    exact absurd hfb hb
  · intro id pg hp _
    obtain ⟨rfl, rfl⟩ := (initC_lookup id pg).1 hp
    exact ⟨fun i j hi => by omega, fun i hi => by omega⟩
  · exact treeKeys.leaf 3 _ none none initC_lookup3 hl (fun i hi => by omega) (fun i hi => by omega)
  · intro id pg hp
    obtain ⟨rfl, rfl⟩ := (initC_lookup id pg).1 hp
    exact ⟨fun _ => rfl, fun h => absurd h hb⟩
  · intro id1 pg1 id2 pg2 h1 h2 hne
    obtain ⟨rfl, rfl⟩ := (initC_lookup id1 pg1).1 h1
    obtain ⟨rfl, rfl⟩ := (initC_lookup id2 pg2).1 h2
    exact absurd rfl hne
  · intro id pg hp
    obtain ⟨rfl, rfl⟩ := (initC_lookup id pg).1 hp
    rw [emptyPg_overflow]; show 3 + 1 ≤ 4; omega
  · intro id pg _ hp _ i hi
    obtain ⟨rfl, rfl⟩ := (initC_lookup id pg).1 hp
    omega

theorem initC_flFileOK : flFileOK initImg initC := by
  intro f hf
  cases hf
  simp only
  rw [initImg_page2]
  have hc : flCountIdx (emptyPg 2 (W16 16)) = (0, 0) := by
    unfold flCountIdx; rw [emptyPg_count]; rfl
  have hids : flIds (emptyPg 2 (W16 16)) = [] := by unfold flIds; rw [hc]; rfl
  rw [emptyPg_overflow, emptyPg_flags, hc, hids, emptyPg_length]
  refine ⟨Nat.le_refl _, by show 2 + 1 ≤ 4; omega, rfl, by omega, List.nodup_nil,
    fun x hx => absurd hx List.not_mem_nil, fun x hx => absurd hx List.not_mem_nil, ?_,
    emptyPg_id _ _ (by omega)⟩
  intro s h1 h2 hcov
  have := initC_coversSlot s hcov
  omega

theorem initC_treeData : treeData initC = ∅ := by
  have hl : pageFlags (emptyPg 3 (W16 2)) = leafPageFlag := by rw [emptyPg_flags]; rfl
  unfold treeData treeEntries treeLeaves
  rw [show initC.root = 3 from rfl]
  generalize initC.pages.size = n
  simp only [leavesF, initC_lookup3, hl, ↓reduceIte, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, leafEnts, emptyPg_count, List.range_zero, List.map_nil]
  rfl

/-- **`fileOK`'s facts of the image `init` writes.** -/
theorem initImg_ok :
    fileImage initImg initC ∧ initC.metaOk ∧ treeOK initC ∧ flFileOK initImg initC ∧
      initC.hwm * 4096 ≤ initImg.length ∧ 1 ≤ initC.txid ∧ initC.txid < 2 ^ 62 ∧
      treeData initC = ∅ := by
  refine ⟨initC_fileImage, initC_metaOk, initC_treeOK, initC_flFileOK, ?_, ?_, ?_,
    initC_treeData⟩
  · rw [initImg_length]; show 4 * 4096 ≤ 16384; omega
  · show 1 ≤ 1; omega
  · show 1 < 2 ^ 62; omega

end image

end bbolt
end EtcdGrove
end Perennial
