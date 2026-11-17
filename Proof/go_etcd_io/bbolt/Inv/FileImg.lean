/-
The image of a database file (split from `Inv/FileHolds.lean`, session bbolt-inv, so that the
lock resources, `Inv/Locks.lean`, can hold a closed database's file, `closedR`'s stash): a
committed state's image in a file's bytes (`fileImage`, `flFileOK`, `fileOK`), its txid's time
receipt (`fileRcpt`), and `fileHoldsDef`.
-/
module

public import Proof.go_etcd_io.bbolt.Model.Store
public import Perennial.GooseLang.Receipts
public import Proof.os.Base

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

/-- **Two committed states with the same metas, both well formed, have one txid at most the
other's**: the current meta of each is valid and at its txid's parity slot; of two at different
slots, `metaOk` makes the other slot's valid meta older (session bbolt-inv, `fileRcpt`). -/
theorem metaOk_txid_le (C C' : CommitSt) (h0 : C'.m0 = C.m0) (h1 : C'.m1 = C.m1)
    (hC : C.metaOk) (hC' : C'.metaOk) : C'.txid ≤ C.txid := by
  have hs : ∀ i, C'.slot i = C.slot i := by intro i; unfold CommitSt.slot; rw [h0, h1]
  obtain ⟨-, -, -, -, -, -, hm, hnext⟩ := hC
  obtain ⟨-, -, -, -, -, hv', hm', -⟩ := hC'
  rw [hs] at hv' hm'
  by_cases hp : C'.txid % 2 = C.txid % 2
  · have e : C.slot C'.txid = C.slot C.txid := by unfold CommitSt.slot; rw [hp]
    rw [e] at hm'
    have := hm'.1.symm.trans hm.1
    omega
  · have e : C.slot C'.txid = C.slot (C.txid + 1) := by
      unfold CommitSt.slot
      by_cases ha : C'.txid % 2 = 0
      · have hb : (C.txid + 1) % 2 = 0 := by omega
        rw [if_pos ha, if_pos hb]
      · have hb : ¬ (C.txid + 1) % 2 = 0 := by omega
        rw [if_neg ha, if_neg hb]
    rw [e] at hv' hm'
    have := hnext hv'
    rw [hm'.1] at this
    omega

/-- Two images of one file's bytes, both well formed: the one txid is at most the other's. -/
theorem fileImage_txid_le (xs : List w8) (C C' : CommitSt) (h : fileImage xs C) (hm : C.metaOk)
    (h' : fileImage xs C') (hm' : C'.metaOk) : C'.txid ≤ C.txid :=
  metaOk_txid_le C C' (h'.1.trans h.1.symm) (h'.2.1.trans h.2.1.symm) hm hm'

end image

section holds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The file's txid has been reached** (session bbolt-inv): the persistent time receipt of a
bound on the txid of every well-formed committed state the bytes `xs` are an image of (or there
is none: an empty file). bbolt's txids count commits, each of them a counted step of the program
(`Commit`'s meta write raises `metaR`'s receipt), so a txid is below `receiptBound GF`: what lets
`Close` give a file back after commits (`fileOK`'s `txid < 2 ^ 62` from `receiptBound GF ≤ 2 ^ 62`,
`Open`'s premise), where a bare bound would not survive an open, commits and a close. -/
def fileRcpt (xs : List w8) : IProp GF :=
  iprop(⌜∀ C, fileImage xs C → ¬ C.metaOk⌝ ∨
    ∃ t : Nat, ⧖ t ∗ ⌜∀ C, fileImage xs C → C.metaOk → C.txid ≤ t⌝)

instance fileRcpt_persistent (xs : List w8) : Persistent (fileRcpt (GF := GF) xs) := by
  unfold fileRcpt; infer_instance

instance fileRcpt_timeless (xs : List w8) : Timeless (fileRcpt (GF := GF) xs) := by
  unfold fileRcpt; infer_instance

/-- `fileRcpt` of an image of `C` from `C`'s txid's receipt. -/
theorem fileRcpt_intro (xs : List w8) (C : CommitSt) (h : fileImage xs C) (hm : C.metaOk) :
    ⧖ C.txid ⊢ fileRcpt (GF := GF) xs := by
  unfold fileRcpt
  iintro #H
  iright
  iexists C.txid
  iframe H
  ipureintro
  exact fun C' h' hm' => fileImage_txid_le xs C C' h hm h' hm'

/-- `fileRcpt` gives the receipt of the txid of any well-formed image. -/
theorem fileRcpt_get (xs : List w8) (C : CommitSt) (h : fileImage xs C) (hm : C.metaOk) :
    fileRcpt (GF := GF) xs ⊢ ⧖ C.txid := by
  unfold fileRcpt
  iintro (%hn | ⟨%t, #Ht, %hle⟩)
  · exact absurd hm (hn C h)
  · iapply preceipt_mono (hle C h hm) $$ Ht

/-- The facts of a well-formed file image of `D` (its current meta's txid at least `1`: `init`
writes txid 1 as the current meta, a commit only raises it; batch 6). -/
def fileOK (xs : List w8) (size : Nat) (D : Data) : Prop :=
  (size = 0 ∧ D = ∅) ∨
  ∃ C, fileImage xs C ∧ C.metaOk ∧ treeOK C ∧ flFileOK xs C ∧ C.hwm * 4096 ≤ size ∧
    1 ≤ C.txid ∧ C.txid < 2 ^ 62 ∧ treeData C = D

/-- **The file of inode `i` holds a database with the data `D`** (what `fileHolds` is sealed
to): its whole `OsMeta`, with no mapping, and all of its page-cache bytes, whose values are an
image of `D` (`fileOK`; a fresh, empty file holds `∅`). The bytes' crash candidates are not
looked at (bbolt's specs are in-process). Its txid's time receipt (`fileRcpt`, session
bbolt-inv). The file's size is whole pages (session bbolt-inv: every file bbolt writes is, `init`'s
and `DB.grow`'s truncates; `Close` gives back no partial page) and below `2 ^ 62` (maintainer 12, item
5: true of every file bbolt writes, whose mapping is at most `maxMapSize = 2 ^ 48`; `Open`'s
`metasZero` and `mmap` need it). "No file at the path" is not a state of the file: it is the
tree's (`pathHolds`, `Spec/go_etcd_io/bbolt/Api.lean`). -/
def fileHoldsDef (i : Ino) (D : Data) : IProp GF :=
  iprop(∃ (m : OsMeta) (xs : List ByteG), osMeta i (DFrac.own 1) m ∗
      osBytes i 0 (DFrac.own 1) xs ∗
      ⌜m.maps = ∅ ∧ xs.length = m.size ∧ (m.size < 2 ^ 62 ∧ m.size % 4096 = 0) ∧
        fileOK (xs.map Prod.fst) m.size D⌝ ∗
      fileRcpt (xs.map Prod.fst))

/-! ## Lemma statements (U11) -/

instance fileHoldsDef_timeless (i : Ino) (D : Data) :
    Timeless (fileHoldsDef (GF := GF) i D) := by
  have : ∀ off dq xs, Timeless (osBytes (GF := GF) i off dq xs) := fun _ _ _ => by
    unfold osBytes bytesG; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)
  unfold fileHoldsDef; infer_instance

/-- An empty file is no image of a well-formed state (its metas are no 4096 bytes). -/
theorem fileImage_nil_not (C : CommitSt) (h : fileImage [] C) : ¬ C.metaOk := by
  intro hm
  have h0 := hm.1
  rw [h.1] at h0
  simp [bytesAt] at h0

end holds

end bbolt
end EtcdGrove
end Perennial
