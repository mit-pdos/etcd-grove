/-
U7c's (`notes/bbolt-proof-plan.md`) pure layer of `Cursor.node`: its loop's state (`curSt`: the
writer's state `Y` reached from `X` by materializations of the bucket `bl`, the bucket's record
kept but for its caches and root node, every cached node a live node of `bl`, the logical tree
kept by data), its start, its step (`nodeAdded`), and what it gives the next step.
-/
module

public import Proof.go_etcd_io.bbolt.Write.Mat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section curnode
variable [GooseExts]

/-- Every cached node of `BY` is a non-nil live node of bucket `bl`. -/
def nmOK (Y : WX) (bl : Loc) (BY : BRec) : Prop :=
  ∀ c l, BY.nm !! c = some l → l ≠ null ∧ ∃ r, BY.ns !! l = some r ∧ r.nv.bucket' = bl ∧ l ∈ Y.live

/-- **`Cursor.node`'s loop state**: `Y` is `X` with bucket `bl` (record `B` in `X`) grown by
materializations; the record's header, page, inline page and source kept; its cache grown and
pointing at live nodes of `bl`; the logical tree of `bl` kept by data (at position `0` only for
an inline bucket). -/
def curSt (X Y : WX) (bl : Loc) (B : BRec) : Prop :=
  matGrow X Y bl ∧ (wOK X → wOK Y) ∧ Y.v = X.v ∧ Y.t.pm = X.t.pm ∧ bl ∈ Y.live ∧
  ∃ BY, Y.t.bs !! bl = some BY ∧ BY.ib = B.ib ∧ BY.bv.nodes' = B.bv.nodes' ∧
    BY.bv.page' = B.bv.page' ∧ BY.ipg = B.ipg ∧ BY.isrc = B.isrc ∧ BY.pst = B.pst ∧
    (∀ c l, B.nm !! c = some l → BY.nm !! c = some l) ∧ nmOK Y bl BY ∧
    ∀ pid, (B.ib.root' = W64 0 → pid = W64 0) → ldat (ltree Y bl pid) = ldat (ltree X bl pid)

omit [GooseExts] in
private theorem cmem_self {V : Type} (m : GMap Loc V) (k : Loc) (v : V) : k ∈ m.insert k v := by
  rw [GMap.mem_iff]; show ((m.insert k v) !! k).isSome = true; rw [GMap.lookup_insert]; rfl

omit [GooseExts] in
private theorem cmem_of {V : Type} {m : GMap Loc V} {k k' : Loc} (v : V) (h : k' ∈ m) :
    k' ∈ m.insert k v := by
  rw [GMap.mem_iff] at h ⊢
  show ((m.insert k v) !! k').isSome = true
  by_cases hk : k = k'
  · subst hk; rw [GMap.lookup_insert]; rfl
  · rw [GMap.lookup_insert_ne _ _ hk]; exact h

theorem matGrow_snoc (X Y Z : WX) (bl l : Loc) (pgid : w64) (parent : Loc)
    (h : matGrow X Y bl) (hadd : nodeAdded Y Z bl l pgid parent) (hpos : matPos Y bl pgid parent) :
    matGrow X Z bl := by
  induction h with
  | refl X bl => exact matGrow.step _ _ _ _ _ _ _ hadd hpos (matGrow.refl _ _)
  | step X Y0 Y bl l0 pgid0 parent0 hadd0 hpos0 _ ih =>
    exact matGrow.step _ _ _ _ _ _ _ hadd0 hpos0 (ih hadd hpos)

/-- A searchable bucket's cache is `nmOK`. -/
theorem nmOK_of_local (X : WX) (bl : Loc) (B : BRec) (hb : bktLocalOK X bl)
    (hB : X.t.bs !! bl = some B) : nmOK X bl B := by
  obtain ⟨-, B0, hB0, hc, -, -, hlv, -⟩ := hb
  rw [hB] at hB0; cases hB0
  intro c l hcl
  obtain ⟨hl, r, hr, -⟩ := hc.2.2.2.2.1 c l hcl
  exact ⟨hl, r, hr, (hc.2.2.2.2.2.2.2.1 l r hr).1, hlv l r hr⟩

/-- **The loop's start.** -/
theorem curSt_refl (X : WX) (bl : Loc) (B : BRec) (hb : bktLocalOK X bl)
    (hB : X.t.bs !! bl = some B) : curSt X X bl B :=
  ⟨matGrow.refl X bl, id, rfl, rfl, hb.1, B, hB, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ h => h,
    nmOK_of_local X bl B hb hB, fun _ _ => rfl⟩

/-- The page positions of `Y` are `X`'s (`wpageAt` reads only the header's root, the page field
and the inline page). -/
theorem curSt_wpageAt (X Y : WX) (bl : Loc) (B BY : BRec) (hv : Y.v = X.v) (hib : BY.ib = B.ib)
    (hpg : BY.bv.page' = B.bv.page') (hipg : BY.ipg = B.ipg) (pid : w64) :
    wpageAt Y.v BY pid = wpageAt X.v B pid := by
  unfold wpageAt; rw [hv, hib, hpg, hipg]

/-- **`matReady` carries over** to the loop's state. -/
theorem curSt_ready (X Y : WX) (bl : Loc) (B BY : BRec) (h : curSt X Y bl B)
    (hBY : Y.t.bs !! bl = some BY) (pid : w64) (hr : matReady X B pid) : matReady Y BY pid := by
  obtain ⟨-, -, hv, hpm, -, BY0, hBY0, hib, -, hpg, hipg, hisrc, hpst, -⟩ := h
  rw [hBY] at hBY0; cases hBY0
  obtain ⟨pa, pg, hw, h1, h2, h3, h4, h5, h6, h7⟩ := hr
  refine ⟨pa, pg, by rw [curSt_wpageAt X Y bl B BY hv hib hpg hipg]; exact hw, h1, h2, h3, h4,
    by rw [hpm]; exact h5, ?_, h7⟩
  rw [hib, hpst, hisrc]; exact h6

/-- A location no object has is no cached node (`nmOK`). -/
theorem nmOK_fresh (Y : WX) (bl : Loc) (BY : BRec) (hBY : Y.t.bs !! bl = some BY)
    (hn : nmOK Y bl BY) (l : Loc) (hl : (Y.t.objs !! l).isNone) : ∀ c, BY.nm !! c ≠ some l := by
  intro c hc
  obtain ⟨-, r, hr, -⟩ := hn c l hc
  have := objs_isSome_node Y.t bl BY l hBY (by simp [hr])
  simp_all

/-- **The loop's step**: a materialization of `bl` (at a position of `Y`, fresh: for an inline
bucket, without a root node) keeps the loop's state and caches the new node at its position. -/
theorem curSt_step (X Y Y' : WX) (bl l : Loc) (pid : w64) (parent : Loc) (B : BRec)
    (h : curSt X Y bl B) (hadd : nodeAdded Y Y' bl l pid parent) (hpos : matPos Y bl pid parent)
    (hinl : ∀ BY, Y.t.bs !! bl = some BY → BY.ib.root' = W64 0 → BY.bv.rootNode' = null) :
    curSt X Y' bl B ∧ ∃ BY', Y'.t.bs !! bl = some BY' ∧ BY'.nm !! pid = some l := by
  obtain ⟨hg, hok, hv, hpm, hlv, BY, hBY, hib, hnd, hpg, hipg, hisrc, hpst, hnmB, hnm, hld⟩ := h
  have hfr : matFresh Y bl l := by
    intro BY0 hBY0
    rw [hBY] at hBY0; cases hBY0
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hlo, -⟩ := hadd
    exact ⟨nmOK_fresh Y bl BY hBY hnm l hlo, hinl BY hBY⟩
  have hlt := ltree_nodeAdded' Y Y' bl l pid parent hadd hfr
  have hg' := matGrow_snoc X Y Y' bl l pid parent hg hadd hpos
  have hok' : wOK X → wOK Y' := fun h0 => wOK_nodeAdded Y Y' bl l pid parent (hok h0) hadd hpos
  obtain ⟨BY0, pa, pg, r, ns', bv', hBY0, hwp, hnm0, hl0, hlo, hrb, hrp, hrid, hrleaf, hru, hrs,
    hrcs, hrco, hrws, hrlive, hrkey, hrks, hrins, hrkn, hrvs, hcase, hX'⟩ := hadd
  rw [hBY] at hBY0; cases hBY0
  have hlo' : Y.t.objs !! l = none := by simpa using hlo
  have hns'l : ns' !! l = some r := by
    rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', -, -, -, -, -, -, -, -, -, rfl⟩ <;>
      exact GMap.lookup_insert _ _ _
  -- the old nodes keep their bucket in `ns'`
  have hns'o : ∀ y ry, BY.ns !! y = some ry → ∃ ry', ns' !! y = some ry' ∧
      ry'.nv.bucket' = ry.nv.bucket' := by
    intro y ry hy
    have hyl : y ≠ l := by
      intro e; subst e
      have := objs_isSome_node Y.t bl BY y hBY (by simp [hy]); rw [hlo'] at this; cases this
    rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', hrp, -, -, -, -, -, -, -, hnv, rfl⟩
    · exact ⟨ry, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hyl)]; exact hy, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hyl)]
      by_cases hyp : parent = y
      · subst hyp
        rw [hrp] at hy; cases hy
        refine ⟨rp', GMap.lookup_insert _ _ _, ?_⟩
        rw [hnv]
      · exact ⟨ry, by rw [GMap.lookup_insert_ne _ _ hyp]; exact hy, rfl⟩
  have hbv : bv'.page' = BY.bv.page' ∧ bv'.nodes' = BY.bv.nodes' := by
    rcases hcase with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> exact ⟨rfl, rfl⟩
  subst hX'
  refine ⟨⟨hg', hok', by rw [← hv], by rw [← hpm], cmem_of () hlv, _,
    GMap.lookup_insert _ _ _, hib, by rw [hbv.2, hnd], by rw [hbv.1, hpg], hipg, hisrc, hpst,
    ?_, ?_, ?_⟩, _, GMap.lookup_insert _ _ _, GMap.lookup_insert _ _ _⟩
  · intro c l0 hc
    have h1 := hnmB c l0 hc
    show (BY.nm.insert pid l) !! c = some l0
    by_cases hcp : pid = c
    · subst hcp; rw [hnm0] at h1; cases h1
    · rw [GMap.lookup_insert_ne _ _ hcp]; exact h1
  · intro c l0 hc
    change (BY.nm.insert pid l) !! c = some l0 at hc
    by_cases hcp : pid = c
    · subst hcp
      rw [GMap.lookup_insert] at hc; cases hc
      exact ⟨hl0, r, hns'l, hrb, cmem_self _ _ _⟩
    · rw [GMap.lookup_insert_ne _ _ hcp] at hc
      obtain ⟨hn0, ry, hry, hryb, hryl⟩ := hnm c l0 hc
      obtain ⟨ry', hry', hb'⟩ := hns'o l0 ry hry
      exact ⟨hn0, ry', hry', by rw [hb', hryb], cmem_of () hryl⟩
  · intro p hp
    rw [hlt bl p (fun _ BY0 hBY0 hin => by rw [hBY] at hBY0; cases hBY0; exact hp (hib ▸ hin))]
    exact hld p hp

/-- An inline bucket's logical tree is a leaf at every position (`bktClean`: its nodes are
leaves, its inline page is a leaf page). -/
theorem ltree_inline_leaf (X : WX) (hwm : Nat) (bl : Loc) (B : BRec)
    (hB : X.t.bs !! bl = some B) (hc : bktClean X.v hwm bl B) (hin : B.ib.root' = W64 0)
    (pid : w64) (lf : Bool) (ws : List WEntry) (h : ltree X bl pid = some (lf, ws)) : lf = true := by
  unfold ltree at h
  rw [hB] at h
  simp only at h
  unfold resolve at h
  rw [if_pos hin] at h
  by_cases hrn : B.bv.rootNode' = null
  · rw [if_pos hrn] at h
    simp only at h
    obtain ⟨lp, hlp, e⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, -, hg, -⟩ := hc.1 hin hrn
    unfold wpageAt at hlp
    rw [if_pos hin] at hlp
    split at hlp
    · simp only [Option.some.injEq] at hlp
      subst hlp
      rw [← e.1]; simp [hg.2.1]
    · cases hlp
  · rw [if_neg hrn] at h
    simp only at h
    obtain ⟨r, hr, e⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at e
    rw [← e.1]
    exact hc.2.2.2.2.2.2.1 hin _ r hr

/-- A file bucket's `resolve` is its cache. -/
theorem resolve_file (B : BRec) (hin : B.ib.root' ≠ W64 0) (pid : w64) :
    resolve B pid = B.nm !! pid := by
  unfold resolve; rw [if_neg hin]

/-- The root position resolves to the root node, cached at the root's page id (`bktClean`). -/
theorem resolve_root_nm (v : View) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean v hwm bl B)
    (l : Loc) (h : resolve B B.ib.root' = some l) : B.nm !! B.ib.root' = some l := by
  unfold resolve at h
  by_cases hin : B.ib.root' = W64 0
  · rw [if_pos hin] at h
    by_cases hrn : B.bv.rootNode' = null
    · rw [if_pos hrn] at h; cases h
    · rw [if_neg hrn] at h; cases h
      exact hc.2.2.2.1 hrn
  · rw [if_neg hin] at h; exact h

/-- With no node at the root position, the bucket has no root node (`bktClean`). -/
theorem resolve_root_none (v : View) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean v hwm bl B)
    (h : resolve B B.ib.root' = none) : B.bv.rootNode' = null := by
  unfold resolve at h
  by_cases hin : B.ib.root' = W64 0
  · rw [if_pos hin] at h
    by_cases hrn : B.bv.rootNode' = null
    · exact hrn
    · rw [if_neg hrn] at h; cases h
  · rw [if_neg hin] at h
    by_cases hrn : B.bv.rootNode' = null
    · exact hrn
    · have := hc.2.2.2.1 hrn; rw [h] at this; cases this

end curnode

end Write

end bbolt
end EtcdGrove
end Perennial
