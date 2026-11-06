/-
U7j (`notes/bbolt-proof-plan.md`): what `CreateBucket` and `DeleteBucket` read off the root
bucket's search, pure.
- `posI_leaf_flag`: a leaf a search of a `wOK` writer's bucket reaches holds bucket entries iff
  the bucket is the root (`leafShape` for a node, `posShape` for a view page, `inlineGood` for an
  inline bucket's page, which is never the root's: `rootNotInline`);
- `root_lookup`: after a search of the root bucket for `kb`, the writer's data has the bucket `kb`
  iff the search lands on an entry of key `kb` (`lRoutes_found'`, `route_found_at`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.WOpenOK
public import Proof.go_etcd_io.bbolt.Read.LRoutes
public import Proof.go_etcd_io.bbolt.Write.DataBkt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section createbkt
variable [GooseExts]

/-- A 32-bit flag word's bucket bit is its value's parity. -/
theorem isBktFlag_iff_mod (x : Nat) (h : x < 2 ^ 32) :
    isBktFlag (W32 (x : Int)) ↔ x % 2 = 1 := by
  unfold isBktFlag
  have h2 : (W32 (x : Int)).toNat = x := by
    rw [BitVec.toNat_ofInt]; simp; omega
  have hk : (W32 (x : Int) &&& W32 1).toNat = x % 2 := by
    rw [BitVec.toNat_and, h2]
    show x &&& 1 = x % 2
    rw [Nat.and_one_is_mod]
  constructor
  · intro hb
    have : (W32 (x : Int) &&& W32 1).toNat ≠ 0 := by
      intro h0; apply hb; apply BitVec.eq_of_toNat_eq; rw [h0]; rfl
    rw [hk] at this; omega
  · intro h1 h0
    have := congrArg BitVec.toNat h0
    rw [hk] at this; simp at this; omega

/-- **The entries of a leaf a search reaches** (a `posI` position of a searchable bucket of a
`wOK` writer): bucket entries exactly in the root bucket. -/
theorem posI_leaf_flag (X : WX) (bl : Loc) (B : BRec) (hok : wOK X) (hB : X.t.bs !! bl = some B)
    (p : w64) (hI : WOpen.posI X B p) (ws : List WEntry) (hL : ltree X bl p = some (true, ws))
    (w : WEntry) (hw : w ∈ ws) : isBktFlag w.flags ↔ bl = X.rl := by
  have hcl := ((hok.1.2.2.2.2.2 bl B hB).1)
  rcases hI with ⟨l, rn, hres, hrn⟩ | ⟨h0, hrn0, rfl⟩ | ⟨h0, hwf, hfree, ⟨c, hpr, hown⟩, -⟩
  · rw [ltree_node X bl B p l rn hB hres hrn] at hL
    simp only [Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨hlf, rfl⟩ := hL
    exact hok.1.2.1.2.2.1 bl B hB l rn hrn hlf w hw
  · -- an inline bucket's page: plain entries, and the bucket is not the root
    have hg := (hcl.1 h0 hrn0).2.2.1
    have hres : resolve B (W64 0) = none := by simp [resolve, h0, hrn0]
    have hwp : wpageAt X.v B (W64 0) = some (B.bv.page', B.ipg) := by simp [wpageAt, h0]
    rw [ltree_page X bl B _ _ _ hB hres hwp] at hL
    simp only [Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨-, rfl⟩ := hL
    simp only [pageWs, List.mem_map, List.mem_range] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    have hne : bl ≠ X.rl := by
      intro e; subst e; exact hok.1.2.1.2.2.2.2 B hB h0
    have hf := (hg.2.2.2.2 i hi).2
    simp only [pageW, hg.2.1, ↓reduceIte]
    rw [isBktFlag_iff_mod _ (WOpen.leafFlags_lt _ _)]
    constructor
    · intro h; omega
    · intro h; exact absurd h hne
  · -- a view page under a page position: `posShape`
    have hnm : B.nm !! p = none := by
      have := hfree p.toNat (treeHas.root _ _ (WOpen.treeWF_page hwf).choose_spec.1)
      simpa using this
    have hres : resolve B p = none := by unfold resolve; rw [if_neg h0]; exact hnm
    obtain ⟨pg, hpg, -⟩ := WOpen.treeWF_page hwf
    have hwp : wpageAt X.v B p = some (X.v.base +ₗ ((p.toNat * 4096 : Nat) : Int), pg) := by
      unfold wpageAt; rw [if_neg h0, hpg]; rfl
    rw [ltree_page X bl B _ _ _ hB hres hwp] at hL
    simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hL
    obtain ⟨hlf, rfl⟩ := hL
    simp only [pageWs, List.mem_map, List.mem_range] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    have hs := (hok.1.2.1.2.2.2.1 bl B hB c p.toNat pg hpr hown hpg hlf i hi).1
    simp only [pageW, hlf, ↓reduceIte]
    rw [isBktFlag_iff_mod _ (WOpen.leafFlags_lt _ _), ← hs]
    rfl

/-- **The leaf a search ends at** holds bucket entries exactly in the root bucket. -/
theorem lLeaf_flag (X : WX) (bl : Loc) (B : BRec) (hok : wOK X) (hB : X.t.bs !! bl = some B)
    (hb : bktLocalOK X bl) (els : List elemRef) (pids : List w64) (hp : lPath X bl els pids)
    (w : WEntry) (hw : w ∈ lLeaf X bl pids) : isBktFlag w.flags ↔ bl = X.rl := by
  obtain ⟨p, ws, ⟨j, hpj⟩, hL, hle⟩ := WOpen.lPath_leaf X bl B hB hb els pids hp
  have hpI := WOpen.lPath_posI X bl B hB hb els pids hp j p hpj
  rw [hle] at hw
  exact posI_leaf_flag X bl B hok hB p hpI ws hL w hw

/-- **The root bucket's data, as a search finds it**: after a search of the root bucket for `kb`,
the writer's data has the bucket `kb` iff the search lands on an entry of key `kb`. -/
theorem root_lookup (X : WX) (B : BRec) (hok : wOK X) (hB : X.t.bs !! X.rl = some B)
    (hb : bktLocalOK X X.rl) (els : List elemRef) (pids : List w64) (kb : List w8)
    (hp : lPath X X.rl els pids) (hr : lRoutes X X.rl els pids kb) :
    ((wtxData X) !! kb).isSome ↔ wsFound (lLeaf X X.rl pids) kb := by
  rw [wtxData_lookup, ← lRoutes_found' X X.rl els pids kb hb hp hr]
  unfold bktData
  rw [Option.isSome_map, List.find?_isSome]
  constructor
  · rintro ⟨e, he, hek⟩
    simp only [decide_eq_true_eq] at hek
    unfold rootEnts at he
    obtain ⟨ws, hws, hm⟩ := List.mem_flatMap.1 he
    obtain ⟨w, hw, hwe⟩ := List.mem_filterMap.1 hm
    by_cases hf : isBktFlag w.flags
    · simp only [hf, decide_true, ↓reduceIte, Option.some.injEq] at hwe
      subst hwe
      exact ⟨w, List.mem_flatten.2 ⟨ws, hws, hw⟩, hek⟩
    · simp [hf] at hwe
  · rintro ⟨w, hw, hk⟩
    have hat := WOpen.route_found_at X X.rl els pids kb hb hp hr w hw hk
    have hwl : w ∈ lLeaf X X.rl pids := List.mem_of_getElem? hat
    have hf := (lLeaf_flag X X.rl B hok hB hb els pids hp w hwl).2 rfl
    refine ⟨(w.key, w.value), ?_, by simp [hk]⟩
    unfold WX.allEnts at hw
    obtain ⟨ws, hws, hw'⟩ := List.mem_flatten.1 hw
    unfold rootEnts
    exact List.mem_flatMap.2 ⟨ws, hws, List.mem_filterMap.2 ⟨w, hw', by simp [hf]⟩⟩

end createbkt

end Write

end bbolt
end EtcdGrove
end Perennial
