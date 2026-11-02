/-
The pages of a database file, and the pages a tree reaches (pure, but for `slotsView`).

The file `bs` is cut into slots of `ps` bytes (slot `s`: `slotAt bs ps s`). Page `id` starts at
slot `id` and spans `1 + overflow` slots (`pageAt`); `filePages bs ps n` maps every id below
`n` to its page, so pages overlap when one overflows (the pure model, `TxModel.lean`'s
`treeWF`, does not care). The heap does: the database holds the mapped cells slot by slot
(`slotsView`), and a page's bytes are the bytes of its slots (`pageAt_slots`).

`treeHas pages root id`: page `id` is a page of the tree rooted at page `root` (the root, a
branch's children's trees, and the trees of the nested buckets in its leaves: a nested bucket
with a root page, or inline in its value). `treePages` is the part of `pages` a tree reaches
(the pages a read transaction sees).
-/
module

public import Proof.go_etcd_io.bbolt.TxModel
public import Proof.go_etcd_io.bbolt.PageView

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

/-- Slot `s` of the file `bs`: its `ps` bytes from `s * ps`. -/
def slotAt (bs : List w8) (ps s : Nat) : List w8 := (bs.drop (s * ps)).take ps

/-- The number of slots page `id` spans: 1 and its overflow (read from its header). -/
def pageSpan (bs : List w8) (ps id : Nat) : Nat := 1 + pageOverflow (slotAt bs ps id)

/-- Page `id` of the file `bs`: its slots. -/
def pageAt (bs : List w8) (ps id : Nat) : List w8 :=
  (bs.drop (id * ps)).take (pageSpan bs ps id * ps)

/-- The pages of `bs` below `n`. -/
def filePages (bs : List w8) (ps n : Nat) : GMap Nat (List w8) :=
  GMap.mapSeq 0 ((List.range n).map (pageAt bs ps))

theorem filePages_lookup (bs : List w8) (ps n id : Nat) :
    filePages bs ps n !! id = if id < n then some (pageAt bs ps id) else none := by
  unfold filePages
  rw [GMap.lookup_map_seq_0]
  split
  · simp [*]
  · simp; omega

/- The pages of a tree in `pages`: `treeHas pages root id` (from the page `root`),
`pageHas pages pg id` (from the page with bytes `pg`), `bucketHas pages v id` (from the
nested bucket with value `v`). -/
mutual
inductive treeHas (pages : GMap Nat (List w8)) : Nat → Nat → Prop
  | root (root : Nat) (pg : List w8) : pages !! root = some pg → treeHas pages root root
  | sub (root : Nat) (pg : List w8) (id : Nat) :
      pages !! root = some pg → pageHas pages pg id → treeHas pages root id

inductive pageHas (pages : GMap Nat (List w8)) : List w8 → Nat → Prop
  | child (pg : List w8) (i id : Nat) :
      pageFlags pg = branchPageFlag → i < pageCount pg → treeHas pages (branchPgid pg i) id →
      pageHas pages pg id
  | bucket (pg : List w8) (i id : Nat) :
      pageFlags pg = leafPageFlag → i < pageCount pg → leafFlags pg i % 2 = bucketLeafFlag →
      bucketHas pages (leafValue pg i) id → pageHas pages pg id

inductive bucketHas (pages : GMap Nat (List w8)) : List w8 → Nat → Prop
  | file (v : List w8) (id : Nat) :
      inBucketRoot v ≠ 0 → treeHas pages (inBucketRoot v) id → bucketHas pages v id
  | inline (v : List w8) (id : Nat) :
      inBucketRoot v = 0 → pageHas pages (inlinePage v) id → bucketHas pages v id
end

open Classical in
/-- The pages of `pages` the tree rooted at `root` reaches. -/
def treePages (pages : GMap Nat (List w8)) (root : Nat) : GMap Nat (List w8) :=
  GMap.filter (fun id _ => decide (treeHas pages root id)) pages

/-- The slots a page of `pages` covers (page `id` covers `id` to `id + overflow`). -/
def coversSlot (pages : GMap Nat (List w8)) (s : Nat) : Prop :=
  ∃ id pg, pages !! id = some pg ∧ id ≤ s ∧ s < id + (1 + pageOverflow pg)

/-- No two pages of `pages` share a slot. -/
def pagesDisjoint (pages : GMap Nat (List w8)) : Prop :=
  ∀ id1 pg1 id2 pg2, pages !! id1 = some pg1 → pages !! id2 = some pg2 → id1 ≠ id2 →
    id1 + (1 + pageOverflow pg1) ≤ id2 ∨ id2 + (1 + pageOverflow pg2) ≤ id1

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The mapped cells (at `data`) of the slots `ss` of the file `bs`, at the fraction `q s`
each. -/
def slotsView (data : Loc) (bs : List w8) (ps : Nat) (q : Nat → Qp) (ss : List Nat) :
    IProp GF :=
  [∗list] s ∈ ss, bytesPointsto (data +ₗ ((s * ps : Nat) : Int)) (DFrac.own (q s)) (slotAt bs ps s)

theorem slot_length (bs : List w8) (ps s : Nat) (h : (s + 1) * ps ≤ bs.length) :
    (slotAt bs ps s).length = ps := by
  unfold slotAt
  simp only [List.length_take, List.length_drop]
  have : (s + 1) * ps = s * ps + ps := by rw [Nat.succ_mul]
  omega

/-- The `k` slots from `id` on (inside the file) are the bytes there. -/
theorem slots_bytes (data : Loc) (bs : List w8) (ps : Nat) (q : Qp) (k : Nat) :
    ∀ (id : Nat), (id + k) * ps ≤ bs.length →
    bytesPointsto (GF := GF) (data +ₗ ((id * ps : Nat) : Int)) (DFrac.own q)
        ((bs.drop (id * ps)).take (k * ps)) ⊣⊢
      [∗list] s ∈ List.range' id k,
        bytesPointsto (data +ₗ ((s * ps : Nat) : Int)) (DFrac.own q) (slotAt bs ps s) := by
  induction k with
  | zero =>
    intro id _
    simp only [Nat.zero_mul, List.take_zero, List.range'_zero]
    exact bytesPointsto_nil _ _
  | succ k ih =>
    intro id h
    have h1 : (id + 1 + k) * ps ≤ bs.length := by
      have : id + 1 + k = id + (k + 1) := by omega
      rw [this]; exact h
    have hs : (id + 1) * ps ≤ bs.length := by
      have := Nat.mul_le_mul_right ps (show id + 1 ≤ id + (k + 1) by omega); omega
    have Hsplit : (bs.drop (id * ps)).take ((k + 1) * ps) =
        slotAt bs ps id ++ (bs.drop ((id + 1) * ps)).take (k * ps) := by
      unfold slotAt
      rw [show (k + 1) * ps = ps + k * ps by rw [Nat.succ_mul, Nat.add_comm], List.take_add,
        List.drop_drop, Nat.succ_mul]
    have Hoff : ((id * ps : Nat) : Int) + (ps : Int) = (((id + 1) * ps : Nat) : Int) := by
      rw [Nat.succ_mul, Int.natCast_add]
    rw [List.range'_succ, Hsplit]
    refine (bytesPointsto_app _ _ _ _).trans ?_
    refine Iris.BI.BiEntails.trans ?_ BigSepL.bigSepL_cons.symm
    rw [slot_length bs ps id hs, loc_add_assoc, Hoff]
    exact sep_congr .rfl (ih (id + 1) h1)

/-- Page `id` (inside the file) is the bytes of its slots. -/
theorem pageAt_slots (data : Loc) (bs : List w8) (ps : Nat) (q : Qp) (id : Nat)
    (h : (id + pageSpan bs ps id) * ps ≤ bs.length) :
    bytesPointsto (GF := GF) (data +ₗ ((id * ps : Nat) : Int)) (DFrac.own q) (pageAt bs ps id) ⊣⊢
      [∗list] s ∈ List.range' id (pageSpan bs ps id),
        bytesPointsto (data +ₗ ((s * ps : Nat) : Int)) (DFrac.own q) (slotAt bs ps s) :=
  slots_bytes data bs ps q _ id h

end preds

end bbolt
end EtcdGrove
end Perennial
