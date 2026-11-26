/-
**The bytes `Tx.WriteTo` writes are a database image** (session S4, pure): a read transaction's
`WriteTo` writes two meta pages (`wtMetas`: its meta copy at slot `txid % 2`, and the same meta
with the txid decremented at the other slot, each `metaBuf`'s layout) and then the file's bytes
from slot 2 to the high-water mark. When those bytes agree with the store's (`g`) on every slot
of the reader's committed tree and of its synced freelist page, the whole is an image of the
reader's data (`writeTo_fileOK`), of a committed state (`wtSt C`) with the reader's txid, so that
no well-formed image of it has a higher txid (`writeTo_txid_le`: what `fileRcpt` takes).

Stated over the unfolded `boltImage` (`Spec/go_etcd_io/bbolt/Api.lean`, sealed there): the
caller folds it.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.FileImg
public import Proof.go_etcd_io.bbolt.Model.FlPg
public import Proof.go_etcd_io.bbolt.Commit.MetaBuf
public import Proof.go_etcd_io.bbolt.Spill.STree
public import Proof.go_etcd_io.bbolt.Read.TreeFacts

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Spill Read
open go_etcd_io.bbolt.internal.common

section wt
variable [GooseExts]

/-! ## The two meta pages -/

/-- The meta of the page `WriteTo` writes at the slot its meta is not on: the txid decremented
(`page.Meta().DecTxid()`). -/
def metaDec (mv : Meta) : Meta := { mv with txid' := mv.txid' - 1 }

/-- Meta slot 0 of what `WriteTo` writes from the meta `mv`. -/
def wtMeta0 (mv : Meta) : List w8 :=
  if mv.txid'.toNat % 2 = 0 then metaBuf mv else metaBuf (metaDec mv)

/-- Meta slot 1 of what `WriteTo` writes from the meta `mv`. -/
def wtMeta1 (mv : Meta) : List w8 :=
  if mv.txid'.toNat % 2 = 0 then metaBuf (metaDec mv) else metaBuf mv

/-- **The two meta pages `WriteTo` writes** (8192 bytes, in slot order). -/
def wtMetas (mv : Meta) : List w8 := wtMeta0 mv ++ wtMeta1 mv

theorem wtMetas_eq (mv : Meta) :
    wtMetas mv = if mv.txid'.toNat % 2 = 0 then metaBuf mv ++ metaBuf (metaDec mv)
      else metaBuf (metaDec mv) ++ metaBuf mv := by
  unfold wtMetas wtMeta0 wtMeta1; split <;> rfl

theorem wtMeta0_length (mv : Meta) : (wtMeta0 mv).length = 4096 := by
  unfold wtMeta0; split <;> exact metaBuf_length _

theorem wtMeta1_length (mv : Meta) : (wtMeta1 mv).length = 4096 := by
  unfold wtMeta1; split <;> exact metaBuf_length _

theorem wtMetas_length (mv : Meta) : (wtMetas mv).length = 8192 := by
  unfold wtMetas; rw [List.length_append, wtMeta0_length, wtMeta1_length]

/-- The header id `metaBuf` gives the current meta's page: its slot. -/
theorem metaHdr_id (mv : Meta) : (metaHdr mv).id'.toNat = mv.txid'.toNat % 2 := by
  simp [metaHdr, zeroHdr, BitVec.toNat_umod]

/-- **The header id `metaBuf` gives the decremented page: the other slot** (the txid at least 1;
`WriteTo` sets the header id to the slot before `DecTxid`, and `metaBuf (metaDec mv)` has the id
`(txid - 1) % 2`). -/
theorem metaHdr_metaDec_id (mv : Meta) (h : 1 ≤ mv.txid'.toNat) :
    (metaHdr (metaDec mv)).id'.toNat = (mv.txid'.toNat + 1) % 2 := by
  rw [metaHdr_id]
  show (mv.txid' - 1).toNat % 2 = _
  have h1 : (1 : w64).toNat = 1 := rfl
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1]; exact h), h1]
  omega

/-- **The committed state `WriteTo`'s bytes are an image of**: the reader's `C`, with the two meta
pages it writes. -/
def wtSt (C : CommitSt) : CommitSt :=
  { C with m0 := wtMeta0 (metaOf (C.slot C.txid)), m1 := wtMeta1 (metaOf (C.slot C.txid)) }

/-! The projections of `wtSt C` and of the summed metas, as rewrites: a `rfl` between `wtSt C`'s
field and `C`'s makes the kernel compare `wtSt C` with `C` first, unfolding `metaBuf`'s checksum. -/

theorem wtSt_m0 (C : CommitSt) : (wtSt C).m0 = wtMeta0 (metaOf (C.slot C.txid)) := by
  unfold wtSt; rfl
theorem wtSt_m1 (C : CommitSt) : (wtSt C).m1 = wtMeta1 (metaOf (C.slot C.txid)) := by
  unfold wtSt; rfl
theorem wtSt_pages (C : CommitSt) : (wtSt C).pages = C.pages := by unfold wtSt; rfl
theorem wtSt_root (C : CommitSt) : (wtSt C).root = C.root := by unfold wtSt; rfl
theorem wtSt_hwm (C : CommitSt) : (wtSt C).hwm = C.hwm := by unfold wtSt; rfl
theorem wtSt_txid (C : CommitSt) : (wtSt C).txid = C.txid := by unfold wtSt; rfl
theorem wtSt_flpg (C : CommitSt) : (wtSt C).flpg = C.flpg := by unfold wtSt; rfl

theorem metaSummed_pageSize (mv : Meta) : (metaSummed mv).pageSize' = mv.pageSize' := by
  unfold metaSummed; rfl
theorem metaSummed_txid (mv : Meta) : (metaSummed mv).txid' = mv.txid' := by
  unfold metaSummed; rfl
theorem metaSummed_root (mv : Meta) : (metaSummed mv).root' = mv.root' := by
  unfold metaSummed; rfl
theorem metaSummed_pgid (mv : Meta) : (metaSummed mv).pgid' = mv.pgid' := by
  unfold metaSummed; rfl
theorem metaSummed_freelist (mv : Meta) : (metaSummed mv).freelist' = mv.freelist' := by
  unfold metaSummed; rfl
theorem metaFlpg_metaSummed (mv : Meta) : metaFlpg (metaSummed mv) = metaFlpg mv := by
  unfold metaFlpg; rw [metaSummed_freelist]
theorem metaDec_txid (mv : Meta) : (metaDec mv).txid' = mv.txid' - 1 := by
  unfold metaDec; rfl

theorem isMeta_metaSummed (C C' : CommitSt) (mv : Meta) (h : C.isMeta mv) (ht : C'.txid = C.txid)
    (hr : C'.root = C.root) (hh : C'.hwm = C.hwm) (hf : C'.flpg = C.flpg) :
    C'.isMeta (metaSummed mv) := by
  unfold CommitSt.isMeta at h ⊢
  rw [ht, hr, hh, hf, metaSummed_txid, metaSummed_root, metaSummed_pgid, metaFlpg_metaSummed]
  exact h

/-- The written metas are well formed: the current one is the reader's (summed), the other's
txid is one less. -/
theorem wtSt_metaOk (C : CommitSt) (hmeta : C.metaOk) (htx1 : 1 ≤ C.txid) : (wtSt C).metaOk := by
  obtain ⟨-, -, hps, -, -, hv, hism, -⟩ := hmeta
  have hpsz := hps C.txid hv
  have hm0 := wtSt_m0 C
  have hm1 := wtSt_m1 C
  generalize hmv : metaOf (C.slot C.txid) = mv at hv hism hpsz hm0 hm1
  have ht : mv.txid'.toNat = C.txid := hism.1
  have hslot : ∀ i, (wtSt C).slot i =
      if i % 2 = C.txid % 2 then metaBuf mv else metaBuf (metaDec mv) := by
    intro i
    unfold CommitSt.slot
    rw [hm0, hm1]
    unfold wtMeta0 wtMeta1
    rw [ht]
    rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
    rcases Nat.mod_two_eq_zero_or_one C.txid with hc | hc <;> simp [hi, hc]
  have htx := wtSt_txid C
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm0]; exact wtMeta0_length _
  · rw [hm1]; exact wtMeta1_length _
  · intro i _
    rw [hslot]
    split <;> rw [metaOf_metaBuf, metaSummed_pageSize]
    · exact hpsz
    · unfold metaDec; exact hpsz
  · rw [hm0]; unfold wtMeta0; split <;> exact metaBuf_tail _
  · rw [hm1]; unfold wtMeta1; split <;> exact metaBuf_tail _
  · rw [htx, hslot, if_pos rfl, metaOf_metaBuf]
    exact metaValid_metaSummed mv hv.1 hv.2.1
  · rw [htx, hslot, if_pos rfl, metaOf_metaBuf]
    exact isMeta_metaSummed C (wtSt C) mv hism htx (wtSt_root C) (wtSt_hwm C) (wtSt_flpg C)
  · rw [htx, hslot, if_neg (by omega), metaOf_metaBuf, metaSummed_txid, metaDec_txid]
    intro _
    have h1 : (1 : w64).toNat = 1 := rfl
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1]; omega), h1]
    omega

/-! ## The freelist page -/

/-- The extent of page `f` in the slots `g` (`Inv/Locks.lean`'s `extentBytes`, not imported:
that module is not pure). -/
def extentBytes' (g : Nat → List w8) (f : Nat) : List w8 :=
  (List.range' f (1 + pageOverflow (g f))).flatMap g

theorem flFileOK_iff (xs : List w8) (C : CommitSt) :
    flFileOK xs C ↔ ∀ f, C.flpg = some f → flPgOK C f (filePage xs f) := Iff.rfl

/-- **A reloadable freelist page is an image's** (`flCurOK`), when the committed transactions'
pending ids are below the high-water mark and on no tree page (`flCurOK` lists such an id with
neither: a pending id is a page some committed transaction freed). -/
theorem flCurOK_flPgOK (fl : FLPg) (C : CommitSt) (pg : List w8) (f : Nat)
    (h : flCurOK fl C pg) (hf : C.flpg = some f)
    (hcp : ∀ x, committedPending fl C x → x.toNat < C.hwm ∧ ¬ coversSlot C.pages x.toNat) :
    flPgOK C f pg := by
  obtain ⟨hf2, hfh, -, hflag, hcnt, hnd, hx2, hxout, hsl, -, -, hxs, -, hid⟩ := h f hf
  refine ⟨hf2, hfh, hflag, hcnt, hnd, fun x hx => ⟨hx2 x hx, ?_⟩,
    fun x hx => ⟨hxout x hx, ?_⟩, fun s h1 h2 => (hsl s h1 h2).1, hid⟩
  · rcases hxs x hx with h | h
    · exact (hcp x h).1
    · exact h.1
  · rcases hxs x hx with h | h
    · exact (hcp x h).2
    · exact h.2.2

/-! ## Slots of the written bytes -/

omit [GooseExts] in
theorem wt_bytesAt_slots (xs : List w8) :
    ∀ (k id : Nat), bytesAt xs (4096 * id) (k * 4096) =
      (List.range' id k).flatMap (fun s => bytesAt xs (4096 * s) 4096)
  | 0, id => by simp [bytesAt]
  | k + 1, id => by
    rw [List.range'_succ, List.flatMap_cons, ← wt_bytesAt_slots xs k (id + 1)]
    unfold bytesAt
    rw [show (k + 1) * 4096 = 4096 + k * 4096 by omega, List.take_add, List.drop_drop,
      show 4096 * id + 4096 = 4096 * (id + 1) by omega]

omit [GooseExts] in
theorem wt_flatMap_congr {l : List Nat} {f g : Nat → List w8} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem wt_pageOverflow_append (a b : List w8) (h : 16 ≤ a.length) :
    pageOverflow (a ++ b) = pageOverflow a := by
  unfold pageOverflow pageHdr bytesAt
  simp only [List.drop_zero]
  rw [List.take_append_of_le_length h]

omit [GooseExts] in
/-- **A slot of the written bytes** (from slot 2): the byte-wise agreement of `ys` (the bytes after
the metas, at file offset `i`, index `i - 8192`) with a slot's bytes `x`. -/
theorem wt_slot (m ys x : List w8) (s : Nat) (hm : m.length = 8192) (hs : 2 ≤ s)
    (hx : x.length = 4096) (h : ∀ j < 4096, ys[4096 * s + j - 8192]? = x[j]?) :
    bytesAt (m ++ ys) (4096 * s) 4096 = x := by
  apply List.ext_getElem?
  intro j
  unfold bytesAt
  rw [List.getElem?_take, List.getElem?_drop]
  split
  · rw [List.getElem?_append_right (by omega), hm]; exact h j ‹_›
  · rw [List.getElem?_eq_none (by omega)]

/-- The file's page `id`, when its slots are `g`'s. -/
theorem wt_filePage (xs : List w8) (g : Nat → List w8) (id : Nat)
    (hsl : ∀ s, id ≤ s → s < id + (1 + pageOverflow (g id)) → bytesAt xs (4096 * s) 4096 = g s) :
    filePage xs id = (List.range' id (1 + pageOverflow (g id))).flatMap g := by
  unfold filePage
  rw [hsl id (Nat.le_refl _) (by omega), wt_bytesAt_slots]
  apply wt_flatMap_congr
  intro s hs
  rw [List.mem_range'_1] at hs
  exact hsl s hs.1 hs.2

theorem wt_treeHas_page {P : Pages} {r y : Nat} (h : treeHas P r y) : ∃ pg, P !! y = some pg :=
  treeHas.rec (pages := P)
    (motive_1 := fun _ y _ => ∃ pg, P !! y = some pg)
    (motive_2 := fun _ y _ => ∃ pg, P !! y = some pg)
    (motive_3 := fun _ y _ => ∃ pg, P !! y = some pg)
    (fun _ pg hpg => ⟨pg, hpg⟩) (fun _ _ _ _ _ ih => ih) (fun _ _ _ _ _ _ ih => ih)
    (fun _ _ _ _ _ _ _ ih => ih) (fun _ _ _ _ ih => ih) (fun _ _ _ _ ih => ih) h

omit [GooseExts] in
theorem wt_ofList_lookup {V : Type} (f : Nat → V) :
    ∀ (l : List Nat) (id : Nat), id ∈ l →
      (GMap.ofList (l.map fun i => (i, f i))) !! id = some (f id)
  | [], id, h => by cases h
  | a :: l, id, h => by
    simp only [List.map_cons, GMap.ofList]
    by_cases ha : a = id
    · subst ha; rw [GMap.lookup_insert]
    · rw [GMap.lookup_insert_ne _ _ ha]
      exact wt_ofList_lookup f l id (by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm ha
        · exact h)

/-- A tree page's id is at least 2 (it roots a well-formed tree). -/
theorem wt_tree_page_ge2 (C : CommitSt) (h : treeOK C) (id : Nat) (pg : List w8)
    (hp : C.pages !! id = some pg) : 2 ≤ id := by
  obtain ⟨⟨hwf, -⟩, htp, -⟩ := h
  have hhas : treeHas C.pages C.root id := by
    rw [← htp] at hp
    rw [treePages_lookup] at hp
    split at hp
    · assumption
    · cases hp
  cases treeHas_treeWF C.pages C.hwm hhas hwf with
  | page _ _ h2 _ _ _ _ _ => exact h2

/-! ## The image -/

/-- **`WriteTo`'s bytes are an image of `wtSt C`** (see the file header): the metas `wtMetas` of the
reader's meta, then `ys`, `hwm - 2` slots that agree byte-wise with the store's bytes `g` on the
tree's slots (`hys`) and on the synced freelist page's (`hfl`), whose page is an image's
(`flPgOK`, from `flCurOK` by `flCurOK_flPgOK`). -/
theorem writeTo_image (C : CommitSt) (g : Nat → List w8) (ys : List w8)
    (hmeta : C.metaOk) (htree : treeOK C) (htx1 : 1 ≤ C.txid)
    (hlen : ys.length = (C.hwm - 2) * 4096)
    (hpg : pagesFromBytes g C.pages)
    (hys : ∀ s ∈ treeSlots C, (g s).length = 4096 ∧
      ∀ j < 4096, ys[4096 * s + j - 8192]? = (g s)[j]?)
    (hfl : ∀ f, C.flpg = some f →
      flPgOK C f (extentBytes' g f) ∧
      ∀ s, f ≤ s → s < f + (1 + pageOverflow (g f)) → (g s).length = 4096 ∧
        ∀ j < 4096, ys[4096 * s + j - 8192]? = (g s)[j]?) :
    let bs := wtMetas (metaOf (C.slot C.txid)) ++ ys
    bs.length = C.hwm * 4096 ∧ 2 ≤ C.hwm ∧ fileImage bs (wtSt C) ∧ (wtSt C).metaOk ∧
      treeOK (wtSt C) ∧ flFileOK bs (wtSt C) ∧ (wtSt C).txid = C.txid ∧
      treeData (wtSt C) = treeData C := by
  intro bs
  have hmlen := wtMetas_length (metaOf (C.slot C.txid))
  have htree0 := htree
  obtain ⟨⟨hwf, -⟩, htp, -, hext, -, -⟩ := htree
  have hroot : 2 ≤ C.root ∧ C.root < C.hwm := by
    cases hwf with
    | page _ _ h2 hlt _ _ _ _ => exact ⟨h2, hlt⟩
  have hlenb : bs.length = C.hwm * 4096 := by
    show (wtMetas _ ++ ys).length = _
    rw [List.length_append, hmlen, hlen]
    have : C.hwm = (C.hwm - 2) + 2 := by omega
    rw [this, Nat.add_mul]; omega
  -- the tree's slots
  have hcov : ∀ id pg, C.pages !! id = some pg → ∀ s, id ≤ s → s < id + (1 + pageOverflow pg) →
      s ∈ treeSlots C ∧ 2 ≤ s := fun id pg hp s h1 h2 =>
    ⟨(mem_pagesSlots_iff _ _).2 ⟨id, pg, hp, h1, h2⟩,
      Nat.le_trans (wt_tree_page_ge2 C htree0 id pg hp) h1⟩
  have hpage : ∀ id pg, C.pages !! id = some pg → filePage bs id = pg := by
    intro id pg hp
    obtain ⟨hS, h2⟩ := hcov id pg hp id (Nat.le_refl _) (by omega)
    have hl := (hys id hS).1
    have hpg' := hpg id pg hp
    have hov : pageOverflow (g id) = pageOverflow pg := by
      conv => rhs; rw [hpg']
      rw [show 1 + pageOverflow pg = (1 + pageOverflow pg - 1) + 1 by omega,
        List.range'_succ, List.flatMap_cons, wt_pageOverflow_append _ _ (by omega)]
    rw [wt_filePage bs g id, hov, ← hpg']
    intro s h1 h2'
    rw [hov] at h2'
    obtain ⟨hS', h2s⟩ := hcov id pg hp s h1 h2'
    exact wt_slot _ ys (g s) s hmlen h2s (hys s hS').1 (hys s hS').2
  have hle : pagesLe C.pages (filePages bs C.hwm) := by
    intro id pg hpg
    have hid := hext id pg hpg
    unfold filePages
    rw [wt_ofList_lookup (filePage _) _ id (List.mem_range.2 (by omega)), hpage id pg hpg]
  have htp' : treePages (filePages bs C.hwm) C.root = C.pages := by
    apply GMap.ext
    intro id
    show treePages _ C.root !! id = C.pages !! id
    rw [treePages_lookup]
    by_cases h : treeHas (filePages bs C.hwm) C.root id
    · rw [if_pos h]
      have h' := treeHas_of_le hle C.hwm h hwf
      obtain ⟨pg, hpg⟩ := wt_treeHas_page h'
      rw [hpg]; exact hle id pg hpg
    · rw [if_neg h]
      rcases hc : C.pages !! id with _ | pg
      · rfl
      · exfalso; apply h
        have h1 : treePages C.pages C.root !! id = some pg := by rw [htp]; exact hc
        rw [treePages_lookup] at h1
        split at h1
        · rename_i ht; exact treeHas_le hle ht
        · cases h1
  -- the synced freelist page
  have hflF : flFileOK bs (wtSt C) := by
    rw [flFileOK_iff, wtSt_flpg]
    intro f hf
    obtain ⟨hok, hsl⟩ := hfl f hf
    have hf2 := hok.1
    have hfp : filePage bs f = extentBytes' g f := by
      apply wt_filePage bs g f
      intro s h1 h2
      exact wt_slot _ ys (g s) s hmlen (by omega) (hsl s h1 h2).1 (hsl s h1 h2).2
    rw [hfp]
    unfold flPgOK at hok ⊢
    rw [wtSt_hwm, wtSt_pages]
    exact hok
  -- the metas
  have hm0 : bytesAt bs 0 4096 = (wtSt C).m0 := by
    show bytesAt (wtMeta0 _ ++ wtMeta1 _ ++ ys) 0 4096 = _
    unfold bytesAt
    rw [List.drop_zero, List.append_assoc, List.take_left' (wtMeta0_length _), wtSt_m0]
  have hm1 : bytesAt bs 4096 4096 = (wtSt C).m1 := by
    show bytesAt (wtMeta0 _ ++ wtMeta1 _ ++ ys) 4096 4096 = _
    unfold bytesAt
    rw [List.append_assoc, List.drop_left' (wtMeta0_length _), List.take_left' (wtMeta1_length _),
      wtSt_m1]
  have himg : fileImage bs (wtSt C) := by
    unfold fileImage
    rw [wtSt_pages, wtSt_hwm, wtSt_root]
    exact ⟨hm0.symm, hm1.symm, htp'.symm⟩
  have htr : treeOK (wtSt C) := by
    unfold treeOK
    rw [wtSt_pages, wtSt_hwm, wtSt_root, wtSt_txid]
    exact htree0
  have hdat : treeData (wtSt C) = treeData C := by
    unfold treeData
    rw [wtSt_pages, wtSt_root]
  exact ⟨hlenb, by omega, himg, wtSt_metaOk C hmeta htx1, htr, hflF, wtSt_txid C, hdat⟩

/-- **`WriteTo`'s bytes are an image of the reader's data** (`boltImage`'s unfolding,
`Spec/go_etcd_io/bbolt/Api.lean`). -/
theorem writeTo_fileOK (C : CommitSt) (g : Nat → List w8) (ys : List w8)
    (hmeta : C.metaOk) (htree : treeOK C) (htx1 : 1 ≤ C.txid) (htx2 : C.txid < 2 ^ 62)
    (hhwm : C.hwm * 4096 < 2 ^ 62)
    (hlen : ys.length = (C.hwm - 2) * 4096)
    (hpg : pagesFromBytes g C.pages)
    (hys : ∀ s ∈ treeSlots C, (g s).length = 4096 ∧
      ∀ j < 4096, ys[4096 * s + j - 8192]? = (g s)[j]?)
    (hfl : ∀ f, C.flpg = some f →
      flPgOK C f (extentBytes' g f) ∧
      ∀ s, f ≤ s → s < f + (1 + pageOverflow (g f)) → (g s).length = 4096 ∧
        ∀ j < 4096, ys[4096 * s + j - 8192]? = (g s)[j]?) :
    let bs := wtMetas (metaOf (C.slot C.txid)) ++ ys
    (bs.length < 2 ^ 62 ∧ bs.length % 4096 = 0) ∧ fileOK bs bs.length (treeData C) := by
  intro bs
  obtain ⟨hl, -, himg, hm, ht, hf, htx, hd⟩ := writeTo_image C g ys hmeta htree htx1 hlen hpg hys hfl
  have hl' : bs.length = C.hwm * 4096 := hl
  refine ⟨⟨by omega, by omega⟩, Or.inr ⟨wtSt C, himg, hm, ht, hf, by rw [wtSt_hwm]; omega, ?_, ?_,
    hd⟩⟩
  · rw [htx]; exact htx1
  · rw [htx]; exact htx2

/-- **No well-formed image of `WriteTo`'s bytes has a txid above the reader's** (so `fileRcpt` of
them follows from the reader's txid's receipt: `fileRcpt_intro` of `writeTo_image`'s `wtSt C`). -/
theorem writeTo_txid_le (C : CommitSt) (g : Nat → List w8) (ys : List w8)
    (hmeta : C.metaOk) (htree : treeOK C) (htx1 : 1 ≤ C.txid)
    (hlen : ys.length = (C.hwm - 2) * 4096)
    (hpg : pagesFromBytes g C.pages)
    (hys : ∀ s ∈ treeSlots C, (g s).length = 4096 ∧
      ∀ j < 4096, ys[4096 * s + j - 8192]? = (g s)[j]?)
    (hfl : ∀ f, C.flpg = some f →
      flPgOK C f (extentBytes' g f) ∧
      ∀ s, f ≤ s → s < f + (1 + pageOverflow (g f)) → (g s).length = 4096 ∧
        ∀ j < 4096, ys[4096 * s + j - 8192]? = (g s)[j]?) :
    ∀ C', fileImage (wtMetas (metaOf (C.slot C.txid)) ++ ys) C' → C'.metaOk → C'.txid ≤ C.txid := by
  intro C' h' hm'
  obtain ⟨-, -, himg, hm, -, -, htx, -⟩ := writeTo_image C g ys hmeta htree htx1 hlen hpg hys hfl
  rw [← htx]
  exact fileImage_txid_le _ (wtSt C) C' himg hm h' hm'

end wt

end bbolt
end EtcdGrove
end Perennial
