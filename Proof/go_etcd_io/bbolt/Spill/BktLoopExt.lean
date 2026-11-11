/-
`Bucket.spill`'s root loop (U9x7, `notes/bbolt-proof-plan.md`): **the root bucket's extents are
kept** (`RInv.rootExt`). The extents `Bucket.free` would free (`WX.extents`: a walk of the logical
tree's positions, each its node's page or its page) depend only on the logical tree's shape (its
branches' child page ids), the root position, the fuel, the view's pages and each position's page
id (`posIdOf`). A step that keeps a bucket's records up to sources (`bktKept`: a child's spill,
`extents_kept`) keeps them; materializations and a put into a leaf (`BktLoopExtMat`) too.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureKeep
public import Proof.go_etcd_io.bbolt.Write.FlView

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section ext
variable [GooseExts]

/-- **The extents from their parts.** -/
theorem extents_congr {X X' : WX} {bl : Loc} {B B' : BRec} (hB : X.t.bs !! bl = some B)
    (hB' : X'.t.bs !! bl = some B') (hrp : X'.rootPid bl = X.rootPid bl) (hf : X'.fuel = X.fuel)
    (hv : X'.v.pages = X.v.pages)
    (hshp : ∀ pid, Write.shp (ltree X' bl pid) = Write.shp (ltree X bl pid))
    (hid : ∀ pid, Write.posIdOf B' pid = Write.posIdOf B pid) :
    X'.extents bl = X.extents bl := by
  have hpos : X'.positions bl = X.positions bl := by
    unfold WX.positions; rw [hf, hrp]; exact Write.lposF_congr _ _ bl hshp _ _
  unfold WX.extents; rw [hpos]
  congr 1; funext pid
  rw [Write.posExtent_def, Write.posExtent_def, hB, hB', hv]
  simp only [hid]

/-- A record equal up to sources gives each position the same page id. -/
theorem posIdOf_kept {B B' : BRec} (hs : bktSim B B')
    (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l)) (pid : w64) :
    Write.posIdOf B' pid = Write.posIdOf B pid := by
  unfold Write.posIdOf
  rw [resolve_sim hs]
  cases resolve B pid with
  | none => rfl
  | some l =>
    simp only
    have h := hns l
    cases h1 : B.ns !! l with
    | none =>
      rw [h1] at h
      cases h2 : B'.ns !! l with
      | none => rfl
      | some r' => rw [h2] at h; exact absurd h (by simp [optRel])
    | some r =>
      rw [h1] at h
      cases h2 : B'.ns !! l with
      | none => rw [h2] at h; exact absurd h (by simp [optRel])
      | some r' =>
        rw [h2] at h
        have h' : nodeSim r r' := h
        simp only [Option.map_some, Option.getD_some]
        rw [h'.1]

/-- **A step keeping the bucket's records up to sources keeps its extents.** -/
theorem extents_kept {X X' : WX} {bl : Loc} {B B' : BRec} (hB : X.t.bs !! bl = some B)
    (hB' : X'.t.bs !! bl = some B') (hs : bktSim B B')
    (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l)) (hv : X'.v.pages = X.v.pages)
    (hf : X'.fuel = X.fuel) : X'.extents bl = X.extents bl :=
  extents_congr hB hB' (rootPid_kept hB hB' hs) hf hv
    (fun pid => Write.shp_of_ldat _ _ (ltree_kept hB hB' hs hns hv pid))
    (posIdOf_kept hs hns)

end ext

end Spill

end bbolt
end EtcdGrove
end Perennial
