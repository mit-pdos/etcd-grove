/- Lean-first (no Rocq counterpart).

# The files a crash may leave of bbolt's database file

* `bGood D f`: the crashed file `f` is a bbolt image of the data `D` with `fileHoldsMDef`'s pure
  facts (`fileOK`, whole pages, below `2 ^ 62`, mappable). Its meta pages' tails (bytes 80 to 4096)
  are zero by `fileOK`'s `metaOk` (`fileOK_tails`: every meta page bbolt writes is a zeroed buffer
  with a header and a meta; the next generation's crash invariant needs them). `bGoodU` is the same
  without whole pages.
* `bGoodInit f`: a file `needsInit` accepts (fork `db.go`, `needsInit`, after the init fix): at most
  four pages, every byte it holds (and every byte of the page holding its end, which a crash that
  grows it may bring back) zero or `init`'s byte (`initImg`), and not `init`'s whole image.
* `RefImg X C`: `X` is a reference image of the committed state `C` (`fileOK`'s facts, so zero meta
  tails); `protData X C` its bytes a crash must keep: the extents of `C`'s tree pages and of its
  synced freelist page.
* `fileOK_transfer`: bytes `ys` that agree with a reference image `X` of `C` on `protData X C` are an
  image of `C`'s data, with `C`'s meta slots replaced by `ys`'s, if that committed state is
  `metaOk` (`metaOk_mk` builds it).
-/
module

public import Proof.go_etcd_io.bbolt.Crash.Meta
public import Proof.go_etcd_io.bbolt.Crash.View
public import Proof.go_etcd_io.bbolt.Inv.WriteToImage
public import Proof.go_etcd_io.bbolt.Open.InitImage

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs Spill Read
open go_etcd_io.bbolt.internal.common

section good
variable [GooseExts]

/-! ## The predicates -/

/-- **A good crash image of the data `D`, but for whole pages.** -/
def bGoodU (D : Data) (f : OsFile) : Prop :=
  fileOK f.contents f.size D ∧ f.size < 2 ^ 62 ∧ f.size ≤ 0xFFFFFFFFFFFF

/-- **A good crash image of the data `D`** (see the file header): `fileHoldsMDef`'s pure facts
(`Inv/FileImg.lean`). -/
def bGood (D : Data) (f : OsFile) : Prop :=
  fileOK f.contents f.size D ∧ (f.size < 2 ^ 62 ∧ f.size % 4096 = 0) ∧
    f.size ≤ 0xFFFFFFFFFFFF

theorem bGood_bGoodU {D : Data} {f : OsFile} (h : bGood D f) : bGoodU D f :=
  ⟨h.1, h.2.1.1, h.2.2⟩

theorem bGoodU_bGood {D : Data} {f : OsFile} (h : bGoodU D f) (ha : f.size % 4096 = 0) :
    bGood D f :=
  ⟨h.1, ⟨h.2.1, ha⟩, h.2.2⟩

/-- `init`'s byte at `b`. -/
def initByte (b : Nat) : w8 := initImg.getD b 0

/-- **A file `needsInit` accepts** (see the file header). -/
def bGoodInit (f : OsFile) : Prop :=
  f.size ≤ 16384 ∧ (∀ b, pageIn f.size b = true → f.cache b = 0 ∨ f.cache b = initByte b) ∧
    ¬ (f.size = 16384 ∧ ∀ b < 16384, f.cache b = initByte b)

/-- **A reference image `X` of the committed state `C`**: `fileOK`'s facts (its zero meta tails among
them, `RefImg.tails`). -/
structure RefImg (X : List w8) (C : CommitSt) : Prop where
  img : fileImage X C
  mok : C.metaOk
  tree : treeOK C
  fl : flFileOK X C
  len : C.hwm * 4096 ≤ X.length
  tx1 : 1 ≤ C.txid
  tx2 : C.txid < 2 ^ 62

/-- A reference image has zero meta tails (`metaOk`'s slot tails, `fileImage_tails`). -/
theorem RefImg.tails {X : List w8} {C : CommitSt} (h : RefImg X C) : metaTailsZero X :=
  fileImage_tails X C h.img h.mok

/-- Byte `b` is in the extent of one of `C`'s tree pages. -/
def protPg (C : CommitSt) (b : Nat) : Prop :=
  ∃ id pg, C.pages !! id = some pg ∧ 4096 * id ≤ b ∧ b < 4096 * id + pg.length

/-- Byte `b` is in the extent of `C`'s synced freelist page (its overflow as `X` holds it). -/
def protFl (X : List w8) (C : CommitSt) (b : Nat) : Prop :=
  ∃ f, C.flpg = some f ∧ 4096 * f ≤ b ∧ b < 4096 * (f + (1 + pageOverflow (filePage X f)))

/-- **The data bytes a crash must keep of `C`** (its reference image `X`): its tree pages' and
synced freelist page's extents. -/
def protData (X : List w8) (C : CommitSt) (b : Nat) : Prop := protPg C b ∨ protFl X C b

/-! ## Lists -/

omit [GooseExts] in
theorem bytesAt_congr (xs ys : List w8) (a L : Nat) (hx : a + L ≤ xs.length)
    (hy : a + L ≤ ys.length) (h : ∀ b, a ≤ b → b < a + L → ys[b]? = xs[b]?) :
    bytesAt ys a L = bytesAt xs a L := by
  apply List.ext_getElem?
  intro j
  unfold bytesAt
  rw [List.getElem?_take, List.getElem?_take, List.getElem?_drop, List.getElem?_drop]
  split
  · exact h _ (by omega) (by omega)
  · rfl

theorem cr_pageOverflow_take (pg : List w8) (n : Nat) (h : 16 ≤ n) :
    pageOverflow (pg.take n) = pageOverflow pg := by
  unfold pageOverflow pageHdr bytesAt
  simp only [List.drop_zero, List.take_take, Nat.min_eq_left h]

theorem cr_filePage_overflow (xs : List w8) (id : Nat) :
    pageOverflow (filePage xs id) = pageOverflow (bytesAt xs (4096 * id) 4096) := by
  unfold filePage bytesAt
  rw [cr_pageOverflow_take _ _ (by
      have := Nat.mul_le_mul_right 4096 (Nat.succ_le_succ (Nat.zero_le
        (pageOverflow ((xs.drop (4096 * id)).take 4096)))); omega),
    cr_pageOverflow_take _ _ (by omega)]

/-- **A file page depends only on the bytes of its extent.** -/
theorem filePage_congr (xs ys : List w8) (id L : Nat)
    (hL : (1 + pageOverflow (bytesAt xs (4096 * id) 4096)) * 4096 ≤ L)
    (hx : 4096 * id + L ≤ xs.length) (hy : 4096 * id + L ≤ ys.length)
    (h : ∀ b, 4096 * id ≤ b → b < 4096 * id + L → ys[b]? = xs[b]?) :
    filePage ys id = filePage xs id := by
  have h1 : bytesAt ys (4096 * id) 4096 = bytesAt xs (4096 * id) 4096 :=
    bytesAt_congr xs ys _ _ (by omega) (by omega) (fun b hb1 hb2 => h b hb1 (by omega))
  unfold filePage
  rw [h1]
  exact bytesAt_congr xs ys _ _ (by omega) (by omega) (fun b hb1 hb2 => h b hb1 (by omega))

theorem filePages_lookup (xs : List w8) (hwm id : Nat) :
    filePages xs hwm !! id = if id < hwm then some (filePage xs id) else none := by
  unfold filePages
  have : ∀ l : List Nat, (GMap.ofList (l.map fun i => (i, filePage xs i))) !! id =
      if id ∈ l then some (filePage xs id) else none := by
    intro l
    induction l with
    | nil => simp [GMap.ofList]; rfl
    | cons a l ih =>
      simp only [List.map_cons, GMap.ofList]
      by_cases ha : a = id
      · subst ha; rw [GMap.lookup_insert, if_pos List.mem_cons_self]
      · rw [GMap.lookup_insert_ne _ _ ha, ih]
        have : id ∈ a :: l ↔ id ∈ l := by
          simp only [List.mem_cons]; constructor
          · rintro (h | h)
            · exact absurd h.symm ha
            · exact h
          · exact Or.inr
        by_cases hm : id ∈ l
        · rw [if_pos hm, if_pos (this.2 hm)]
        · rw [if_neg hm, if_neg (fun h => hm (this.1 h))]
  rw [this]; simp only [List.mem_range]

/-! ## Facts of a reference image -/

/-- A tree page of a reference image: its bytes, its extent inside the high-water mark, its id at
least 2. -/
theorem refImg_page {X : List w8} {C : CommitSt} (hR : RefImg X C) {id : Nat} {pg : List w8}
    (hp : C.pages !! id = some pg) :
    filePage X id = pg ∧ 2 ≤ id ∧ pg.length = (1 + pageOverflow pg) * 4096 ∧
      id + (1 + pageOverflow pg) ≤ C.hwm := by
  have htree := hR.tree
  obtain ⟨⟨hwf, -⟩, htp, -, hext, -, -⟩ := hR.tree
  have hhas : treeHas C.pages C.root id := by
    have h1 := hp
    rw [← htp, treePages_lookup] at h1
    split at h1
    · assumption
    · cases h1
  have hfp : filePage X id = pg := by
    have h1 := hp
    rw [hR.img.2.2, treePages_lookup] at h1
    split at h1
    · rw [filePages_lookup] at h1; split at h1
      · cases h1; rfl
      · cases h1
    · cases h1
  have hlen : pg.length = (1 + pageOverflow pg) * 4096 := by
    cases treeHas_treeWF C.pages C.hwm hhas hwf with
    | page _ pg' _ _ hpg' _ hl _ => rw [hp] at hpg'; cases hpg'; exact hl
  exact ⟨hfp, wt_tree_page_ge2 C htree id pg hp, hlen, hext id pg hp⟩

/-- **Every protected data byte lies past the meta pages and below the high-water mark.** -/
theorem protData_range {X : List w8} {C : CommitSt} (hR : RefImg X C) {b : Nat}
    (h : protData X C b) : 8192 ≤ b ∧ b < C.hwm * 4096 := by
  rcases h with ⟨id, pg, hp, h1, h2⟩ | ⟨f, hf, h1, h2⟩
  · obtain ⟨-, h2', hl, he⟩ := refImg_page hR hp
    refine ⟨by omega, ?_⟩
    rw [hl] at h2
    have := Nat.mul_le_mul_right 4096 he
    rw [Nat.add_mul] at this
    omega
  · obtain ⟨hf2, hfh, -⟩ := hR.fl f hf
    refine ⟨by omega, ?_⟩
    have := Nat.mul_le_mul_left 4096 hfh
    rw [Nat.mul_comm 4096 C.hwm] at this
    omega

/-- The high-water mark of a reference image is at least 3 (the root page is at least 2 and below
it), so the meta pages are below it. -/
theorem refImg_hwm {X : List w8} {C : CommitSt} (hR : RefImg X C) : 3 ≤ C.hwm := by
  obtain ⟨⟨hwf, -⟩, -⟩ := hR.tree
  cases hwf with
  | page _ _ h2 hlt _ _ _ _ => omega

/-! ## The transfer -/

/-- **Bytes agreeing with a reference image on the protected bytes have `C`'s tree pages.** -/
theorem treePages_transfer (X ys : List w8) (C : CommitSt) (hR : RefImg X C)
    (hlen : C.hwm * 4096 ≤ ys.length) (hag : ∀ b, protData X C b → ys[b]? = X[b]?) :
    treePages (filePages ys C.hwm) C.root = C.pages := by
  obtain ⟨⟨hwf, -⟩, htp, -⟩ := hR.tree
  have hpage : ∀ id pg, C.pages !! id = some pg → filePage ys id = pg := by
    intro id pg hp
    obtain ⟨hfp, -, hl, he⟩ := refImg_page hR hp
    have hend : 4096 * id + pg.length ≤ C.hwm * 4096 := by
      rw [hl]; have := Nat.mul_le_mul_right 4096 he; rw [Nat.add_mul] at this; omega
    rw [← hfp]
    refine filePage_congr X ys id pg.length ?_ (by have := hR.len; omega) (by omega)
      (fun b h1 h2 => hag b (.inl ⟨id, pg, hp, h1, h2⟩))
    rw [hl, ← cr_filePage_overflow, hfp]; exact Nat.le_refl _
  have hle : pagesLe C.pages (filePages ys C.hwm) := by
    intro id pg hpg
    obtain ⟨-, -, -, he⟩ := refImg_page hR hpg
    rw [filePages_lookup, if_pos (by omega), hpage id pg hpg]
  apply GMap.ext
  intro id
  show treePages _ C.root !! id = C.pages !! id
  rw [treePages_lookup]
  by_cases h : treeHas (filePages ys C.hwm) C.root id
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

/-- **Bytes agreeing with a reference image on the protected bytes have its synced freelist
page.** -/
theorem filePage_fl_transfer (X ys : List w8) (C : CommitSt) (hR : RefImg X C)
    (hlen : C.hwm * 4096 ≤ ys.length) (hag : ∀ b, protData X C b → ys[b]? = X[b]?) (f : Nat)
    (hf : C.flpg = some f) : filePage ys f = filePage X f := by
  obtain ⟨-, hfh, -⟩ := hR.fl f hf
  have hend : 4096 * f + (1 + pageOverflow (filePage X f)) * 4096 ≤ C.hwm * 4096 := by
    have := Nat.mul_le_mul_right 4096 hfh; rw [Nat.add_mul] at this; omega
  refine filePage_congr X ys f ((1 + pageOverflow (filePage X f)) * 4096) ?_
    (by have := hR.len; omega) (by omega) (fun b h1 h2 => hag b (.inr ⟨f, hf, h1, by omega⟩))
  rw [cr_filePage_overflow]; exact Nat.le_refl _

/-- **The transfer** (see the file header). -/
theorem fileOK_transfer (X ys : List w8) (C : CommitSt) (hR : RefImg X C)
    (hlen : C.hwm * 4096 ≤ ys.length) (hag : ∀ b, protData X C b → ys[b]? = X[b]?)
    (hm : ({ C with m0 := bytesAt ys 0 4096, m1 := bytesAt ys 4096 4096 } : CommitSt).metaOk) :
    fileOK ys ys.length (treeData C) := by
  refine Or.inr ⟨{ C with m0 := bytesAt ys 0 4096, m1 := bytesAt ys 4096 4096 },
    ⟨rfl, rfl, (treePages_transfer X ys C hR hlen hag).symm⟩, hm, hR.tree, ?_, hlen, hR.tx1,
    hR.tx2, rfl⟩
  intro f hf
  have h := hR.fl f hf
  rw [filePage_fl_transfer X ys C hR hlen hag f hf]
  exact h

/-! ## `metaOk` from its parts -/

/-- **`metaOk` from its parts**: two 4096-byte slots with zero tails, the current meta valid and the
record's, page size 4096, the other slot's meta, if valid, of page size 4096 and an older txid. -/
theorem metaOk_mk (C : CommitSt) (h0 : C.m0.length = 4096) (h1 : C.m1.length = 4096)
    (hcv : metaValid (metaOf (C.slot C.txid)))
    (hcps : (metaOf (C.slot C.txid)).pageSize'.toNat = 4096)
    (hcm : C.isMeta (metaOf (C.slot C.txid)))
    (hoth : metaValid (metaOf (C.slot (C.txid + 1))) →
      (metaOf (C.slot (C.txid + 1))).pageSize'.toNat = 4096 ∧
        (metaOf (C.slot (C.txid + 1))).txid'.toNat < C.txid)
    (hz0 : metaTailZero C.m0) (hz1 : metaTailZero C.m1) : C.metaOk := by
  refine ⟨h0, h1, ?_, hz0, hz1, hcv, hcm, fun h => (hoth h).2⟩
  intro i hi
  have hs : C.slot i = C.slot C.txid ∨ C.slot i = C.slot (C.txid + 1) := by
    unfold CommitSt.slot
    rcases Nat.mod_two_eq_zero_or_one i with a | a <;>
    rcases Nat.mod_two_eq_zero_or_one C.txid with b | b <;>
    simp [a, b, show (C.txid + 1) % 2 = 1 - C.txid % 2 by omega]
  rcases hs with e | e <;> rw [e] at hi ⊢
  · exact hcps
  · exact (hoth hi).1

/-! ## A file's bytes -/

theorem contents_getElem? (f : OsFile) (b : Nat) (hb : b < f.size) :
    f.contents[b]? = some (f.cache b) := by
  simp [OsFile.contents, hb]

theorem contents_length' (f : OsFile) : f.contents.length = f.size := by
  simp [OsFile.contents]

/-- A meta slot of a file's bytes, inside it, is its page cache's raw meta. -/
theorem metaSlot_raw (f : OsFile) (j : Nat) (h : 4096 * j + 80 ≤ f.size) :
    bytesAt (bytesAt f.contents (4096 * j) 4096) 16 64 = rawMeta f j := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 64
  · rw [bytesAt_getElem? _ 16 64 k hk, bytesAt_getElem? f.contents (4096 * j) 4096 (16 + k) (by omega),
      contents_getElem? f (4096 * j + (16 + k)) (by omega)]
    simp [rawMeta, hk, Nat.add_assoc]
  · rw [List.getElem?_eq_none (by simp [bytesAt]; omega),
      List.getElem?_eq_none (by simp [rawMeta]; omega)]

theorem rawMeta_length (f : OsFile) (j : Nat) : (rawMeta f j).length = 64 := by
  simp [rawMeta]

end good

end bbolt
end EtcdGrove
end Perennial
