/-
`Bucket.spill`'s root loop's end (U9x5, `notes/bbolt-proof-plan.md`), part 1: **the spill's success
from the root node's spill** (`end_post`), pure. The root node's spill (`spDone`, top case, no
other owner) wrote an `sTree` at the new root page; with the root's slots `D` those `RInv` owns
(`Lroot` and the children's), every base slot is the new tree's or pending, and every slot of the
new tree a base slot or new (`spillOK_of_root'`, `BktFinal.spillOK_of_root` with the owned slots
base or new); the buffers dirty pages of fresh slots (`spillBufs`: the spill step's `bufsOK`, `spG`'s
page-cache clause). The root's shape and data (`hshape`, `hnames`, `hbkts`) are premises here
(`Spill/BktEndEls`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopInv
public import Proof.go_etcd_io.bbolt.Spill.DerefRel

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section post
variable [GooseExts]

/-- **`spillOK` from the root bucket's written tree**, the owned slots `D` base or new (a child's
spilled tree's slots are new). -/
theorem spillOK_of_root' (X X' : WX) (C : CommitSt) (fl fl' : FLPg) (txid : w64)
    (st : List FLStep) (h : Nat) (S D : List Nat)
    (hC : C.pages = X.v.pages) (hv : X'.v.pages = X.v.pages)
    (hmark : X.t.mv.pgid' ≤ X'.t.mv.pgid')
    (hS : sTree (spP X') X'.t.mv.pgid'.toNat X'.rootPage none none h S)
    (hshape : rootShape (treePages (spP X') X'.rootPage) X'.rootPage)
    (htx : X'.t.mv.txid'.toNat < 2 ^ 63)
    (hnames : (treeEntries (treePages (spP X') X'.rootPage) X'.rootPage).map Prod.fst =
      (rootEnts X).map Prod.fst)
    (hbkts : ∀ n v, (n, v) ∈ treeEntries (treePages (spP X') X'.rootPage) X'.rootPage →
      some (bktOfPage (treePages (spP X') X'.rootPage) v) = bktData X n)
    (hfl : fl' = fl.applySteps txid st)
    (hbase : ∀ s ∈ treeSlots C, s ∈ D ∨ s ∈ pendSlots fl')
    (hDdrop : ∀ s ∈ D, s ∈ pgSlots (spP X') S ∨ s ∈ pendSlots fl')
    (hSnew : ∀ s ∈ pgSlots (spP X') S, s ∈ treeSlots C ∨ newSlot st X.t.mv.pgid'.toNat s) :
    spillOK X X' C fl fl' txid := by
  classical
  let D' := D.filter (fun s => decide (s ∈ treeSlots C)) ++
    (pgSlots (spP X') S).filter (fun s => decide (s ∈ treeSlots C))
  apply spillOK_of_root X X' C fl fl' txid st h S D' hC hv hmark hS hshape htx hnames hbkts hfl
  · intro s hs
    rcases hbase s hs with hd | hp
    · exact Or.inl (List.mem_append_left _ (List.mem_filter.2 ⟨hd, by simpa using hs⟩))
    · exact Or.inr hp
  · intro s hs
    rcases List.mem_append.1 hs with h1 | h1
    · exact hDdrop s (List.mem_filter.1 h1).1
    · exact Or.inl (List.mem_filter.1 h1).1
  · intro s hs
    rcases hSnew s hs with hb | hn
    · exact Or.inl (List.mem_append_right _ (List.mem_filter.2 ⟨hs, by simpa using hb⟩))
    · exact Or.inr hn
  · intro s hs
    rcases List.mem_append.1 hs with h1 | h1
    · simpa using (List.mem_filter.1 h1).2
    · simpa using (List.mem_filter.1 h1).2

theorem setBkt_spP (X : WX) (bl : Loc) (B' : BRec) : spP (X.setBkt bl B') = spP X := rfl

theorem setBkt_rootPage_bkRooted {X : WX} {B1 : BRec} {rt : Loc} {pg : w64} :
    (X.setBkt X.rl (bkRooted B1 rt pg)).rootPage = pg.toNat := by
  unfold WX.rootPage WX.setBkt
  simp only [GMap.lookup_insert, Option.map_some, Option.getD_some]
  rfl

/-- **The buffers after the root's spill** (`spillBufs`): the spill step's `bufsOK` (from
`RInv.bufs`) and `spG`'s page-cache clause. -/
theorem end_bufs {X X1 : WX} {w w1 : WDb} {O : List Nat} {st1 : List FLStep} {C : CommitSt}
    (hstep : spStep X X1 w w1 O st1) (hC : w.C = C) (hb : bufsOK X w.C w.fl) (bl : Loc)
    (B' : BRec) : spillBufs (X1.setBkt bl B') C w1.fl := by
  have hG := hstep.2.2.2.1
  refine ⟨fun id => ?_, ?_⟩
  · show (X1.t.pm !! id).isSome = (X1.t.bufs !! id).isSome
    exact Bool.eq_iff_iff.2 (hG.2.2.2.2.2.1 id)
  · have := hstep.2.2.2.2.2.2.2.2 hb
    rw [hC] at this
    exact this

/-- **`spillBufs` at the loop's end with no root node**: `RInv.bufs` and `spG`'s clause. -/
theorem end_bufs_nil {X0 X : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) : spillBufs X w0.C w.fl := by
  refine ⟨fun id => Bool.eq_iff_iff.2 (hI.G.2.2.2.2.2.1 id), ?_⟩
  exact hI.bufs

end post

end Spill

end bbolt
end EtcdGrove
end Perennial
