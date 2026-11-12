/-
`Bucket.spill`'s root loop (U9t, `notes/bbolt-proof-plan.md`): **`node.put`'s premises at the
root leaf the search lands on** (`rinv_putPre'`, `BktLoopStep.rinv_putPre`'s proof). The
materializations of `Cursor.node` (`matGrow`) keep the root bucket searchable (`bktLocalOK`), its
header, the view, the transaction's meta and the logical tree by data (`matGrow_keep`); the leaf
at the path's end is then a clean node of the root (`nodeClean`), a leaf (its position's logical
node is), so not its own parent.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopInv
public import Proof.go_etcd_io.bbolt.Write.MatOK
public import Proof.go_etcd_io.bbolt.Write.Mat

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section put
variable [GooseExts]

/-- **One materialization keeps the bucket searchable.** -/
theorem bktLocalOK_nodeAdded_step {X Y : WX} {bl l : Loc} {pgid : w64} {parent : Loc}
    (hbl : bktLocalOK X bl) (hadd : nodeAdded X Y bl l pgid parent)
    (hpos : matPos X bl pgid parent) : bktLocalOK Y bl := by
  have hv : viewWF X.v := hbl.2.choose_spec.2.2.2.2.2
  refine Write.bktLocalOK_nodeAdded X Y bl l pgid parent hv hbl hadd hpos ?_ ?_
  · obtain ⟨B, pa, pg, r, ns', bv', hB, -, -, hl0, hlo, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      hrvs, hcase, hX'⟩ := hadd
    intro B' r' hb' hr'
    have hB' : Y.t.bs !! bl = some { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' } := by
      rw [hX']; exact GMap.lookup_insert _ _ _
    rw [hB'] at hb'; cases hb'
    have hns'l : ns' !! l = some r := by
      rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', -, -, -, -, -, -, -, -, -, rfl⟩ <;>
        exact GMap.lookup_insert _ _ _
    have e : ns' !! l = some r' := hr'
    rw [hns'l] at e; cases e
    exact hrvs
  · obtain ⟨B, pa, pg, r, ns', bv', hB, -, -, hl0, hlo, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      hrvs, hcase, hX'⟩ := hadd
    have hlo' : X.t.objs !! l = none := by simpa using hlo
    have hfresh : B.ns !! l = none := Write.objs_none X.t l hlo' bl B hB
    have hB' : Y.t.bs !! bl = some { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' } := by
      rw [hX']; exact GMap.lookup_insert _ _ _
    intro B0 B1 rp0 rp1 hb0 hb1 hrp0 hrp1
    rw [hB] at hb0; cases hb0
    rw [hB'] at hb1; cases hb1
    have hpl : parent ≠ l := by intro e; rw [e, hfresh] at hrp0; cases hrp0
    rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', hrp, -, -, -, -, -, -, hco, -, rfl⟩
    · have e : (B.ns.insert l r) !! parent = some rp1 := hrp1
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hpl), hrp0] at e
      cases e; rfl
    · have e : ((B.ns.insert parent rp').insert l r) !! parent = some rp1 := hrp1
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hpl), GMap.lookup_insert] at e
      cases e
      rw [hrp0] at hrp; cases hrp
      exact hco

/-- A searchable bucket's new node is fresh in it (`matFresh`), its root a page. -/
theorem matFresh_of_local {X Y : WX} {bl l : Loc} {pgid : w64} {parent : Loc}
    (hbl : bktLocalOK X bl) (hadd : nodeAdded X Y bl l pgid parent)
    (h0 : ∀ B, X.t.bs !! bl = some B → B.ib.root' ≠ W64 0) : matFresh X bl l := by
  obtain ⟨B, pa, pg, r, ns', bv', hB, -, -, hl0, hlo, -⟩ := hadd
  have hlo' : X.t.objs !! l = none := by simpa using hlo
  have hfresh : B.ns !! l = none := Write.objs_none X.t l hlo' bl B hB
  obtain ⟨-, B', hB', hcl, -⟩ := hbl
  rw [hB] at hB'; cases hB'
  intro B'' hB''
  rw [hB] at hB''; cases hB''
  refine ⟨fun c hc => ?_, fun h => absurd h (h0 B hB)⟩
  obtain ⟨-, r', hr', -⟩ := hcl.2.2.2.2.1 c l hc
  rw [hfresh] at hr'; cases hr'

/-- **What materializations keep** (the bucket's root a page). -/
theorem matGrow_keep {X X' : WX} {bl : Loc} (h : matGrow X X' bl) (hbl : bktLocalOK X bl)
    (h0 : ∀ B, X.t.bs !! bl = some B → B.ib.root' ≠ W64 0) :
    bktLocalOK X' bl ∧ X'.v = X.v ∧ X'.t.mv = X.t.mv ∧
      (∀ B, X.t.bs !! bl = some B → ∃ B', X'.t.bs !! bl = some B' ∧ B'.ib = B.ib) ∧
      ∀ pid, Write.ldat (ltree X' bl pid) = Write.ldat (ltree X bl pid) := by
  induction h with
  | refl => exact ⟨hbl, rfl, rfl, fun B hB => ⟨B, hB, rfl⟩, fun _ => rfl⟩
  | step X Y Z bl l pgid parent hadd hpos _ ih =>
    have hbl' := bktLocalOK_nodeAdded_step hbl hadd hpos
    have hf := matFresh_of_local hbl hadd h0
    have hY : Y.v = X.v ∧ Y.t.mv = X.t.mv ∧
        ∀ B, X.t.bs !! bl = some B → ∃ B', Y.t.bs !! bl = some B' ∧ B'.ib = B.ib := by
      obtain ⟨B, pa, pg, r, ns', bv', hB, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
        -, -, hX'⟩ := hadd
      subst hX'
      refine ⟨rfl, rfl, fun B' hB' => ?_⟩
      rw [hB] at hB'; cases hB'
      exact ⟨_, GMap.lookup_insert _ _ _, rfl⟩
    have h0' : ∀ B, Y.t.bs !! bl = some B → B.ib.root' ≠ W64 0 := by
      obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 (show (X.t.bs !! bl).isSome by
        obtain ⟨-, B, hB, -⟩ := hbl; rw [hB]; rfl)
      obtain ⟨B', hB', hib⟩ := hY.2.2 B hB
      intro B'' hB''
      rw [hB'] at hB''; cases hB''
      rw [hib]; exact h0 B hB
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih hbl' h0'
    refine ⟨i1, i2.trans hY.1, i3.trans hY.2.1, fun B hB => ?_, fun pid => ?_⟩
    · obtain ⟨B', hB', hib⟩ := hY.2.2 B hB
      obtain ⟨B'', hB'', hib'⟩ := i4 B' hB'
      exact ⟨B'', hB'', hib'.trans hib⟩
    · rw [i5 pid]
      exact Write.ltree_nodeAdded' X Y bl l pgid parent hadd hf bl pid
        (fun _ B hB e => absurd e (h0 B hB))

/-- **`node.put`'s premises at the leaf the search lands on** (see the module doc). -/
theorem rinv_putPre' {X0 X : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {X1 : WX}
    (hm : matGrow X X1 X0.rl) {els : List elemRef} {pids : List w64} {k : List w8}
    (hp : lPath X X0.rl els pids) {B1 : BRec} {pid : w64}
    {l : Loc} (hB1 : X1.t.bs !! X0.rl = some B1) (hlast : pids.getLast? = some pid)
    (hres : resolve B1 pid = some l) (hk : ∃ we ∈ X.allEnts X0.rl, we.key = k) :
    ∃ rl, B1.ns !! l = some rl ∧ l ∈ X1.live ∧ rl.nv.bucket' = X0.rl ∧ rl.capOwn = true ∧
      wsSorted rl.ws ∧ wsLive rl.ws ∧ 0 < X1.t.mv.pgid'.toNat ∧ X1.v = X.v ∧
      rl.nv.parent' ≠ l ∧ 0 < k.length ∧ X1.t.bs !! X0.rl = some B1 := by
  have h0 : ∀ B, X.t.bs !! X0.rl = some B → B.ib.root' ≠ W64 0 := by
    intro B hB; rw [hI.rootIb B hB]; exact hI.rootPg
  obtain ⟨hloc1, hv1, hmv1, hib1, hlt1⟩ := matGrow_keep hm hI.rootOK.1 h0
  obtain ⟨B, hB, -⟩ := hI.root
  obtain ⟨B', hB', hib⟩ := hib1 B hB
  rw [hB1] at hB'; cases hB'
  have h1 : B1.ib.root' ≠ W64 0 := by rw [hib]; exact h0 B hB
  obtain ⟨-, B2, hB2, hcl, -, -, hlive, -⟩ := hloc1
  rw [hB1] at hB2; cases hB2
  have hnm : B1.nm !! pid = some l := by unfold resolve at hres; rwa [if_neg h1] at hres
  obtain ⟨-, rl, hrl, -⟩ := hcl.2.2.2.2.1 pid l hnm
  have hnc := hcl.2.2.2.2.2.2.2.1 l rl hrl
  -- the leaf: its position's logical node is one
  have hleaf : rl.nv.isLeaf' = true := by
    obtain ⟨hne, hlen, -, hpath⟩ := hp
    obtain ⟨j, hj⟩ : ∃ j, pids[j]? = some pid ∧ j + 1 = els.length := by
      refine ⟨pids.length - 1, ?_, ?_⟩
      · rw [List.getLast?_eq_getElem?] at hlast; exact hlast
      · have : pids ≠ [] := by intro e; rw [e] at hlast; cases hlast
        have : 0 < pids.length := List.length_pos_iff.2 this
        omega
    obtain ⟨e, he⟩ : ∃ e, els[j]? = some e :=
      ⟨els[j]'(by omega), List.getElem?_eq_getElem _⟩
    obtain ⟨-, lf, ws, hlt, -, hend⟩ := hpath j e pid he hj.1
    have hlf := hend hj.2
    subst hlf
    have h2 := hlt1 pid
    rw [hlt] at h2
    unfold ltree at h2
    rw [hB1] at h2
    simp only at h2
    rw [hres] at h2
    simp only at h2
    rw [hrl] at h2
    simp [Write.ldat] at h2
    exact h2.1
  refine ⟨rl, hrl, hlive l rl hrl, hnc.1, hnc.2.1, hnc.2.2.2.1, hnc.2.2.2.2.2.1, ?_, hv1, ?_, ?_,
    hB1⟩
  · have := (hcl.2.1 h1).1; omega
  · intro e
    obtain ⟨rp, hrp, hrpl, -⟩ := hnc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by
      rw [e]; exact (hcl.2.2.2.2.1 pid l hnm).1)
    rw [e, hrl] at hrp; cases hrp
    rw [hleaf] at hrpl; cases hrpl
  · obtain ⟨we, hwe, rfl⟩ := hk
    exact (hI.entKeys we hwe).1

end put

end Spill

end bbolt
end EtcdGrove
end Perennial
