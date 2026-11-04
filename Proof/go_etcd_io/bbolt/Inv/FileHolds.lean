/-
`fileHolds` (U0a of `notes/bbolt-proof-plan.md`; design §3.11, over D-B's fix): a file with no
mapping, all of whose page-cache bytes the client holds, either fresh (no file, or empty) or the
image of a committed state `C` (`fileImage`) that is `metaOk`, `treeOK`, has a reloadable synced
freelist page (`flFileOK`), whose high-water mark is inside the file and whose txid is below
`2 ^ 62`, holding `D`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Tx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

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
its ids within it, distinct, in `[2, hwm)`, none on its own slots or a tree page's. -/
def flFileOK (xs : List w8) (C : CommitSt) : Prop :=
  ∀ f, C.flpg = some f →
    let pg := filePage xs f
    2 ≤ f ∧ f + (1 + pageOverflow pg) ≤ C.hwm ∧ pageFlags pg = freelistPageFlag ∧
    16 + 8 * (flCountIdx pg).2 + 8 * (flCountIdx pg).1 ≤ pg.length ∧
    (flIds pg).Nodup ∧ (∀ x ∈ flIds pg, 2 ≤ x.toNat ∧ x.toNat < C.hwm) ∧
    (∀ x ∈ flIds pg, ¬ (f ≤ x.toNat ∧ x.toNat < f + (1 + pageOverflow pg)) ∧
      ¬ coversSlot C.pages x.toNat) ∧
    ∀ s, f ≤ s → s < f + (1 + pageOverflow pg) → ¬ coversSlot C.pages s

end image

section holds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The facts of a well-formed file image of `D` (its current meta's txid at least `1`: `init`
writes txid 1 as the current meta, a commit only raises it; batch 6). -/
def fileOK (xs : List w8) (size : Nat) (D : Data) : Prop :=
  (size = 0 ∧ D = ∅) ∨
  ∃ C, fileImage xs C ∧ C.metaOk ∧ treeOK C ∧ flFileOK xs C ∧ C.hwm * 4096 ≤ size ∧
    1 ≤ C.txid ∧ C.txid < 2 ^ 62 ∧ treeData C = D

/-- **The file at `path` holds a database with the data `D`** (what `fileHolds` is sealed
to). -/
def fileHoldsDef (path : GoString) (D : Data) : IProp GF :=
  iprop((osMeta path (DFrac.own 1) none ∗ ⌜D = ∅⌝) ∨
    (∃ (m : OsMeta) (xs : List (w8 × Bool)), osMeta path (DFrac.own 1) (some m) ∗
      osBytes path 0 (DFrac.own 1) xs ∗
      ⌜m.maps = ∅ ∧ xs.length = m.size ∧ fileOK (xs.map Prod.fst) m.size D⌝))

/-! ## Lemma statements (U11) -/

instance fileHoldsDef_timeless (path : GoString) (D : Data) :
    Timeless (fileHoldsDef (GF := GF) path D) := by
  sorry

theorem fileHoldsDef_new (path : GoString) (mo : Option OsMeta) :
    osMeta (GF := GF) path (DFrac.own 1) mo ∗
      (match mo with
       | none => iprop(emp)
       | some m => iprop(⌜m.size = 0 ∧ m.maps = ∅⌝ ∗ osBytes (GF := GF) path 0 (DFrac.own 1) []))
    ⊢ fileHoldsDef path ∅ := by
  sorry

/-- **Decoding for `Open`**: a fresh file, or the initial committed state `C` of a well-formed
one (with its bytes). -/
theorem fileHolds_decode (path : GoString) (D : Data) :
    fileHoldsDef (GF := GF) path D ⊢
      (osMeta path (DFrac.own 1) none ∗ ⌜D = ∅⌝) ∨
      (∃ (m : OsMeta) (xs : List (w8 × Bool)), osMeta path (DFrac.own 1) (some m) ∗
        osBytes path 0 (DFrac.own 1) xs ∗ ⌜m.maps = ∅ ∧ xs.length = m.size⌝ ∗
        (⌜m.size = 0 ∧ D = ∅⌝ ∨
         ∃ C, ⌜fileImage (xs.map Prod.fst) C ∧ C.metaOk ∧ treeOK C ∧
           flFileOK (xs.map Prod.fst) C ∧ C.hwm * 4096 ≤ m.size ∧ 1 ≤ C.txid ∧ C.txid < 2 ^ 62 ∧
           treeData C = D⌝)) := by
  sorry

end holds

end bbolt
end EtcdGrove
end Perennial
