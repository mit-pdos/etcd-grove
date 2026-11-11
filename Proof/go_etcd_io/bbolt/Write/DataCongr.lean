/-
The writer's data reads only the logical tree (U7h, for `Put`/`Delete`): `wtxData` is determined by
`ltree`, the fuel, the root positions, the root bucket's location and cache, and the view's pages.
A node record replaced by `node.put`/`node.del`'s (`withEnts`/`withEntsU`: inodes and the inodes
slice besides the entries) has the logical tree of `withWs` (only the entries).
-/
module

public import Proof.go_etcd_io.bbolt.Model.LTree
public import Proof.go_etcd_io.bbolt.Model.WOps
public import Proof.go_etcd_io.bbolt.Write.DataWalk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write

section congr
variable [GooseExts]

/-- **The data, from the logical tree and the root's cache.** -/
theorem wtxData_congr (X Y : WX) (hl : ltree Y = ltree X) (hf : Y.fuel = X.fuel)
    (hr : ∀ c, Y.rootPid c = X.rootPid c) (hrl : Y.rl = X.rl) (hb : ∀ n, bktLoc Y n = bktLoc X n)
    (hv : Y.v = X.v) : wtxData Y = wtxData X := by
  have hlv : ∀ c, Y.leaves c = X.leaves c := by
    intro c; unfold WX.leaves; rw [hl, hf, hr]
  have hre : rootEnts Y = rootEnts X := by unfold rootEnts; rw [hrl, hlv]
  have hdo : ∀ n v, bktDataOf Y n v = bktDataOf X n v := by
    intro n v
    have e1 := hb n
    unfold bktLoc at e1
    unfold bktDataOf lbktEnts
    rw [e1, hv]
    simp only [hlv]
  unfold wtxData
  rw [hre]
  simp only [hdo]

/-- A node record whose logical content is `ws` (and the same leaf flag). -/
theorem ltree_setNode_eq (X : WX) (bl l : Loc) (B : BRec) (r r' : NRec)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) (hlf : r'.nv.isLeaf' = r.nv.isLeaf') :
    ltree (X.setNode bl l r') = ltree (X.withWs bl l r'.ws) := by
  funext c pid
  unfold ltree WX.setNode WX.withWs WX.setBkt
  rw [hB]
  simp only [hr]
  by_cases hc : c = bl
  · subst hc
    simp only [GMap.lookup_insert]
    have e1 : resolve { B with ns := B.ns.insert l r' } pid = resolve B pid := rfl
    have e2 : resolve { B with ns := B.ns.insert l { r with ws := r'.ws } } pid =
      resolve B pid := rfl
    have e3 : wpageAt X.v { B with ns := B.ns.insert l r' } pid = wpageAt X.v B pid := rfl
    have e4 : wpageAt X.v { B with ns := B.ns.insert l { r with ws := r'.ws } } pid =
      wpageAt X.v B pid := rfl
    rw [e1, e2, e3, e4]
    cases resolve B pid with
    | none => rfl
    | some l' =>
      simp only
      by_cases hl : l' = l
      · subst hl; simp [hlf]
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hl), GMap.lookup_insert_ne _ _ (Ne.symm hl)]
  · simp only [GMap.lookup_insert_ne _ _ (Ne.symm hc)]

/-- **A node record replaced, by its entries**: the data is `withWs`'s (`node.put`'s and
`node.del`'s records keep the leaf flag). -/
theorem wtxData_setNode (X : WX) (bl l : Loc) (B : BRec) (r r' : NRec)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) (hlf : r'.nv.isLeaf' = r.nv.isLeaf') :
    wtxData (X.setNode bl l r') = wtxData (X.withWs bl l r'.ws) := by
  have hS : (X.setNode bl l r').t.bs = X.t.bs.insert bl { B with ns := B.ns.insert l r' } := by
    unfold WX.setNode WX.setBkt; rw [hB]
  apply wtxData_congr
  · exact ltree_setNode_eq X bl l B r r' hB hr hlf
  · rw [withWs_fuel X bl l r'.ws B r hB hr]
    unfold WX.fuel
    have hv : (X.setNode bl l r').v = X.v := by unfold WX.setNode WX.setBkt; rw [hB]
    rw [hS, GMap.map_size_insert_Some _ _ _ _ hB, hv]
  · intro c
    rw [withWs_rootPid X bl l r'.ws B r hB hr]
    unfold WX.rootPid
    rw [hS]
    by_cases hc : c = bl
    · subst hc; rw [GMap.lookup_insert, hB]; rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hc)]
  · unfold WX.setNode WX.setBkt; rw [hB]; rfl
  · intro n
    rw [withWs_bktLoc X bl l r'.ws B r hB hr]
    unfold bktLoc
    rw [hS]
    have hrl : (X.setNode bl l r').rl = X.rl := by unfold WX.setNode WX.setBkt; rw [hB]
    rw [hrl]
    by_cases hc : X.rl = bl
    · rw [← hc] at hB ⊢; rw [GMap.lookup_insert, hB]; rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hc)]
  · unfold WX.setNode WX.setBkt; rw [hB]; rfl

end congr

end Write

end bbolt
end EtcdGrove
end Perennial
