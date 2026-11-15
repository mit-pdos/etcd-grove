/-
`fileHolds` (U0a of `notes/bbolt-proof-plan.md`; design §3.11, over D-B's fix): a file with no
mapping, all of whose page-cache bytes the client holds, either fresh (no file, or empty) or the
image of a committed state `C` (`fileImage`) that is `metaOk`, `treeOK`, has a reloadable synced
freelist page (`flFileOK`), whose high-water mark is inside the file and whose txid is below
`2 ^ 62`, holding `D`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Tx
public import Proof.go_etcd_io.bbolt.Read.TxBytes
public import GooseLang.Ext.Fs.TreeSpecsOpen

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode

section image
variable [GooseExts]

/-- The extent of page `id` of the file's bytes `xs` (its header's overflow). -/
def filePage (xs : List w8) (id : Nat) : List w8 :=
  bytesAt xs (4096 * id) ((1 + pageOverflow (bytesAt xs (4096 * id) 4096)) * 4096)

/-- The file's pages below the high-water mark. -/
def filePages (xs : List w8) (hwm : Nat) : Pages :=
  GMap.ofList ((List.range hwm).map fun id => (id, filePage xs id))

/-- **`xs` is an image of the committed state `C`**: its meta slots, and its tree's pages (the
pages reachable from the root, as the file holds them). -/
def fileImage (xs : List w8) (C : CommitSt) : Prop :=
  C.m0 = bytesAt xs 0 4096 ∧ C.m1 = bytesAt xs 4096 4096 ∧
  C.pages = treePages (filePages xs C.hwm) C.root

/-- **The file's synced freelist page** (when `C` names one): a freelist page within `[2, hwm)`,
its ids within it, distinct, in `[2, hwm)`, none on its own slots or a tree page's, its header
naming its own id (maintainer 14, item 1, decided by the coordinator: `init` writes it with id 2,
`commitFreelist` writes the page `allocate` returns, whose header id `allocate` sets; `Commit`
frees `tx.meta.freelist`'s extent by the header's overflow, `Free`'s `p.Id()`). -/
def flFileOK (xs : List w8) (C : CommitSt) : Prop :=
  ∀ f, C.flpg = some f →
    let pg := filePage xs f
    2 ≤ f ∧ f + (1 + pageOverflow pg) ≤ C.hwm ∧ pageFlags pg = freelistPageFlag ∧
    16 + 8 * (flCountIdx pg).2 + 8 * (flCountIdx pg).1 ≤ pg.length ∧
    (flIds pg).Nodup ∧ (∀ x ∈ flIds pg, 2 ≤ x.toNat ∧ x.toNat < C.hwm) ∧
    (∀ x ∈ flIds pg, ¬ (f ≤ x.toNat ∧ x.toNat < f + (1 + pageOverflow pg)) ∧
      ¬ coversSlot C.pages x.toNat) ∧
    (∀ s, f ≤ s → s < f + (1 + pageOverflow pg) → ¬ coversSlot C.pages s) ∧
    pageId pg = f

end image

section holds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The facts of a well-formed file image of `D` (its current meta's txid at least `1`: `init`
writes txid 1 as the current meta, a commit only raises it; batch 6). -/
def fileOK (xs : List w8) (size : Nat) (D : Data) : Prop :=
  (size = 0 ∧ D = ∅) ∨
  ∃ C, fileImage xs C ∧ C.metaOk ∧ treeOK C ∧ flFileOK xs C ∧ C.hwm * 4096 ≤ size ∧
    1 ≤ C.txid ∧ C.txid < 2 ^ 62 ∧ treeData C = D

/-- **The file of inode `i` holds a database with the data `D`** (what `fileHolds` is sealed
to): its whole `OsMeta`, with no mapping, and all of its page-cache bytes, whose values are an
image of `D` (`fileOK`; a fresh, empty file holds `∅`). The bytes' crash candidates are not
looked at (bbolt's specs are in-process). The file's size is below `2 ^ 62` (maintainer 12, item
5: true of every file bbolt writes, whose mapping is at most `maxMapSize = 2 ^ 48`; `Open`'s
`metasZero` and `mmap` need it). "No file at the path" is not a state of the file: it is the
tree's (`pathHolds`, `Spec/go_etcd_io/bbolt/Api.lean`). -/
def fileHoldsDef (i : Ino) (D : Data) : IProp GF :=
  iprop(∃ (m : OsMeta) (xs : List ByteG), osMeta i (DFrac.own 1) m ∗
      osBytes i 0 (DFrac.own 1) xs ∗
      ⌜m.maps = ∅ ∧ xs.length = m.size ∧ m.size < 2 ^ 62 ∧ fileOK (xs.map Prod.fst) m.size D⌝)

/-! ## Lemma statements (U11) -/

instance fileHoldsDef_timeless (i : Ino) (D : Data) :
    Timeless (fileHoldsDef (GF := GF) i D) := by
  have : ∀ off dq xs, Timeless (osBytes (GF := GF) i off dq xs) := fun _ _ _ => by
    unfold osBytes bytesG; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)
  unfold fileHoldsDef; infer_instance

/-- A file just created holds the empty database. -/
theorem fileHoldsDef_new (i : Ino) :
    osMeta (GF := GF) i (DFrac.own 1) newMeta ⊢ fileHoldsDef i ∅ := by
  unfold fileHoldsDef
  iintro H
  iexists newMeta, []
  iframe H
  isplitl
  · unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  ipureintro
  exact ⟨rfl, rfl, by decide, Or.inl ⟨rfl, rfl⟩⟩

/-- **Decoding for `Open`**: an empty file holding `∅`, or the initial committed state `C` of a
well-formed one (with its bytes). -/
theorem fileHolds_decode (i : Ino) (D : Data) :
    fileHoldsDef (GF := GF) i D ⊢
      (∃ (m : OsMeta) (xs : List ByteG), osMeta i (DFrac.own 1) m ∗
        osBytes i 0 (DFrac.own 1) xs ∗ ⌜m.maps = ∅ ∧ xs.length = m.size ∧ m.size < 2 ^ 62⌝ ∗
        (⌜m.size = 0 ∧ D = ∅⌝ ∨
         ∃ C, ⌜fileImage (xs.map Prod.fst) C ∧ C.metaOk ∧ treeOK C ∧
           flFileOK (xs.map Prod.fst) C ∧ C.hwm * 4096 ≤ m.size ∧ 1 ≤ C.txid ∧ C.txid < 2 ^ 62 ∧
           treeData C = D⌝)) := by
  unfold fileHoldsDef
  iintro ⟨%m, %xs, Hm, Hb, %h⟩
  iexists m, xs
  iframe Hm Hb
  obtain ⟨h1, h2, h0, h3⟩ := h
  isplitr
  · ipureintro; exact ⟨h1, h2, h0⟩
  rcases h3 with h3 | ⟨C, hC⟩
  · ileft; ipureintro; exact h3
  · iright; iexists C; ipureintro; exact hC

end holds

end bbolt
end EtcdGrove
end Perennial
