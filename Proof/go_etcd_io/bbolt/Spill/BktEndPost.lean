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

open Fs

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
  · have := hstep.2.2.2.2.2.2.2.2.1 hb
    rw [hC] at this
    exact this

/-- **`spillBufs` at the loop's end with no root node**: `RInv.bufs` and `spG`'s clause. -/
theorem end_bufs_nil {X0 X : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) : spillBufs X w0.C w.fl := by
  refine ⟨fun id => Bool.eq_iff_iff.2 (hI.G.2.2.2.2.2.1 id), ?_⟩
  exact hI.bufs


/-- **What the root's leaf elements `E` give** of a tree written with them over a page map `P'`
agreeing with `P` on the owned slots `D`: the root shape and the writer's data at the start
(`spillOK_of_root'`'s `hshape`, `hnames`, `hbkts`). -/
def endEls (X0 : WX) (P : Pages) (D : List Nat) (E : List El) : Prop :=
  ∀ (P' : Pages) (root hwm h : Nat) (S : List Nat), sTree P' hwm root none none h S →
    treeEls P' root = E → (∀ x ∈ D, P' !! x = P !! x) →
    rootShape (treePages P' root) root ∧
    (treeEntries (treePages P' root) root).map Prod.fst = (rootEnts X0).map Prod.fst ∧
    ∀ n v, (n, v) ∈ treeEntries (treePages P' root) root →
      some (bktOfPage (treePages P' root) v) = bktData X0 n

theorem setBkt_rootPage_of {X : WX} {bl : Loc} {B' : BRec} (h : X.rl = bl) :
    (X.setBkt bl B').rootPage = B'.ib.root'.toNat := by
  subst h
  unfold WX.rootPage WX.setBkt
  simp only [GMap.lookup_insert, Option.map_some, Option.getD_some]

/-- **The spill's success after the root node's spill** (see the module doc). -/
theorem end_post {X0 X : WX} {w0 w : WDb} {B0 B : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hvC : X.v = View.ofC X.v.base w.C)
    (htx : X0.t.mv.txid'.toNat < 2 ^ 63) (hmv : X.t.mv.txid' = X0.t.mv.txid')
    (hB : X.t.bs !! X0.rl = some B)
    {rn : NRec} {h : Nat} {D : List Nat} {N : List Loc} {E : List El}
    (hDo : ∀ s ∈ Lroot ++ keys.flatMap Dc, s ∈ D) (hDi : ∀ s ∈ D, s ∈ Lroot ++ keys.flatMap Dc)
    (hEls : endEls X0 (spP X) D E) (hunsp : rn.nv.spilled' = false)
    {X1 : WX} {w1 : WDb} {st1 : List FLStep} {B1 : BRec} {rt : Loc} {rr : NRec}
    (hdone : spDone X X1 w w1 X0.rl B.bv.rootNode' rn [] none none h D N E .top st1)
    (hB1 : X1.t.bs !! X0.rl = some B1) (hrr : B1.ns !! rt = some rr)
    (hroot : nodeRootIn B1 B1.bv.rootNode' rt) :
    spillOK X0 (X1.setBkt X0.rl (bkRooted B1 rt rr.nv.pgid')) w0.C w0.fl w1.fl w0.wtxid ∧
      spillBufs (X1.setBkt X0.rl (bkRooted B1 rt rr.nv.pgid')) w0.C w1.fl := by
  obtain ⟨hstep, hc⟩ := hdone
  rcases hc with ⟨hsp, -⟩ | ⟨-, T, D', hfr, -, -, hD1, hD2, hag, -, hm⟩
  · rw [hunsp] at hsp; cases hsp
  obtain ⟨rt', rr', S, h', hnode', -, -, -, hB'r, hsT, hD', hE⟩ := hm
  obtain ⟨B', hB', hroot'⟩ := hB'r
  rw [hB1] at hB'; cases hB'
  obtain ⟨B2, hB2, hsim, -⟩ := hfr.2.2.2.2.2.2.2.2.2.2.2.2.2.1 B hB
  rw [hB1] at hB2; cases hB2
  have hbv : B1.bv = B.bv := hsim.1
  rw [hbv] at hroot
  have hrt : rt' = rt := nodeRootIn_unique hroot' hroot
  subst hrt
  have hrr' : rr' = rr := by
    unfold WX.node at hnode'; rw [hB1] at hnode'; simp only [Option.bind_some] at hnode'
    rw [hrr] at hnode'; cases hnode'; rfl
  subst hrr'
  have hrl1 : X1.rl = X0.rl := hfr.1.trans hI.rl
  have hrp : (X1.setBkt X0.rl (bkRooted B1 rt' rr'.nv.pgid')).rootPage = rr'.nv.pgid'.toNat :=
    setBkt_rootPage_of hrl1
  have hmark1 : X.t.mv.pgid'.toNat ≤ X1.t.mv.pgid'.toNat := hfr.2.2.2.2.2.2.2.2.1
  have hmv1 : X1.t.mv = { X.t.mv with pgid' := X1.t.mv.pgid' } := hfr.2.2.2.2.2.2.2.1
  have hwC : w.C = w0.C := hI.C
  have hcp : w0.C.pages = X0.v.pages := by
    rw [← hwC, ← hI.pages]
    have := congrArg View.pages hvC; simpa [View.ofC] using this.symm
  have hDag : ∀ x ∈ D, spP X1 !! x = spP X !! x := by
    intro x hx
    exact Classical.byContradiction fun hne => hag x hne hx
  have hEls' := hEls (spP X1) rr'.nv.pgid'.toNat _ h' S hsT hE hDag
  refine ⟨?_, end_bufs hstep hwC (hwC ▸ hI.bufs) X0.rl _⟩
  apply spillOK_of_root' X0 _ w0.C w0.fl w1.fl w0.wtxid (st ++ st1) h' S D hcp
  · show X1.v.pages = X0.v.pages
    rw [hstep.2.2.1, hI.pages]
  · show X0.t.mv.pgid' ≤ X1.t.mv.pgid'
    have := hI.mark
    rw [BitVec.le_def]; omega
  · rw [setBkt_spP, hrp]; exact hsT
  · rw [setBkt_spP, hrp]; exact hEls'.1
  · show X1.t.mv.txid'.toNat < 2 ^ 63
    rw [hmv1]; simp only; rw [hmv]; exact htx
  · rw [setBkt_spP, hrp]; exact hEls'.2.1
  · rw [setBkt_spP, hrp]; exact hEls'.2.2
  · rw [hstep.2.1, hI.fl, applySteps_append, wtxid_of_C hwC]
  · intro s hs
    rcases hI.base s hs with ho | hp
    · exact Or.inl (hDo s ho)
    · exact Or.inr (hstep.2.2.2.2.2.1 s hp)
  · intro s hs
    rcases hD1 s hs with h1 | h1
    · rw [setBkt_spP, ← hD']; exact Or.inl h1
    · exact Or.inr h1
  · intro s hs
    rw [setBkt_spP, ← hD'] at hs
    rcases hD2 s hs with h1 | h1
    · rcases hI.new s (hDi s h1) with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (newSlot_mono h2 (fun x hx => List.mem_append_left _ hx) (Nat.le_refl _))
    · exact Or.inr (newSlot_mono h1 (fun x hx => List.mem_append_right _ hx) hI.mark)

end post

end Spill

end bbolt
end EtcdGrove
end Perennial
