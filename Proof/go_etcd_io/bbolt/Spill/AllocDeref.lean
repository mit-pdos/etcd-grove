/-
`allocate` keeps its own premises (U9c, `notes/bbolt-proof-plan.md`, batch 12; pure): through
`dereference`'s step (`derefStep`, U9b's step lemmas), the remap's `WX.rebase` (after `derefOK`
and with the objects disjoint no live node has a view slice left to become stale) and
`WX.addPage` (which touches only the page cache, the buffers and the meta).

`allocRes_derefPre'` and `derefRel_rebase_derefPre'` are `Inv/Ctx`'s `allocRes_derefPre` and
`derefRel_rebase_derefPre` with the premise `objsDisj X.t` added: without it the statements are
false (two buckets sharing a node location, the shadowed record's view slices are not covered by
`derefOK`, which is over `X.t.objs`, and become stale). Callers have it from `wtxHeap`'s `heapOK`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.DerefRel
public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section allocDeref
variable [GooseExts]

/-! ## `WX.addPage` touches none of the premises' fields -/

theorem derefPre_addPage (X : WX) (id : w64) (p : Loc) (count : Nat) (hwm : w64)
    (h : derefPre X) : derefPre (X.addPage id p count hwm) := h

theorem liveFresh_addPage (X : WX) (id : w64) (p : Loc) (count : Nat) (hwm : w64)
    (h : liveFresh X) : liveFresh (X.addPage id p count hwm) := h

theorem bktReach_addPage (X : WX) (id : w64) (p : Loc) (count : Nat) (hwm : w64) {d : Loc}
    (h : bktReach X d) : bktReach (X.addPage id p count hwm) d := by
  induction h with
  | root => exact .root
  | child bl c B n hB hn _ ih => exact .child bl c B n hB hn ih

theorem liveReach_addPage (X : WX) (id : w64) (p : Loc) (count : Nat) (hwm : w64)
    (h : liveReach X) : liveReach (X.addPage id p count hwm) :=
  ⟨fun bl B hB hl => bktReach_addPage X id p count hwm (h.1 bl B hB hl), h.2⟩

/-! ## The remap's re-base -/

-- `NRec.unview` (a node after a remap, `BRec.unview`'s nodes): `Inv/WtxHeap` (batch 14).

theorem rebase_bs (X : WX) (b bl : Loc) :
    (X.rebase b).t.bs !! bl = (X.t.bs !! bl).map BRec.unview := by
  simp [WX.rebase, GMap.lookup_fmap]

theorem unview_ns (B : BRec) (l : Loc) : B.unview.ns !! l = (B.ns !! l).map NRec.unview := by
  simp only [BRec.unview, GMap.lookup_fmap]; rfl

theorem unview_bv (B : BRec) : B.unview.bv = B.bv := rfl
theorem unview_bm (B : BRec) : B.unview.bm = B.bm := rfl

theorem NRec.unview_keys (r : NRec) : r.unview.ws.map WEntry.key = r.ws.map WEntry.key := by
  simp [NRec.unview, WEntry.unview, Function.comp_def]

theorem rebase_bs_some {X : WX} {b bl : Loc} {B' : BRec} (h : (X.rebase b).t.bs !! bl = some B') :
    ∃ B, X.t.bs !! bl = some B ∧ B' = B.unview := by
  rw [rebase_bs] at h
  obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨B, hB, rfl⟩

theorem unview_ns_some {B : BRec} {l : Loc} {r' : NRec} (h : B.unview.ns !! l = some r') :
    ∃ r, B.ns !! l = some r ∧ r' = r.unview := by
  rw [unview_ns] at h
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨r, hr, rfl⟩

theorem nodeRootIn_unview {B : BRec} {n rt : Loc} (h : nodeRootIn B n rt) :
    nodeRootIn B.unview n rt := by
  induction h with
  | top n r hr hp => exact .top n r.unview (by rw [unview_ns, hr]; rfl) hp
  | up n rt r hr hp _ ih => exact .up n rt r.unview (by rw [unview_ns, hr]; rfl) hp ih

theorem descIn_unview {B : BRec} {n d : Loc} (h : descIn B n d) : descIn B.unview n d := by
  induction h with
  | self n => exact .self n
  | child n c d r hr hc _ ih => exact .child n c d r.unview (by rw [unview_ns, hr]; rfl) hc ih

theorem bktReach_rebase (X : WX) (b : Loc) {d : Loc} (h : bktReach X d) :
    bktReach (X.rebase b) d := by
  induction h with
  | root => exact .root
  | child bl c B n hB hn _ ih =>
    exact .child bl c B.unview n (by rw [rebase_bs, hB]; rfl) hn ih

theorem derefPre_rebase (X : WX) (b : Loc) (hp : derefPre X) : derefPre (X.rebase b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro bl B' l r' hB' hr' hl
    obtain ⟨B, hB, rfl⟩ := rebase_bs_some hB'
    obtain ⟨r, hr, rfl⟩ := unview_ns_some hr'
    obtain ⟨h0, h1, h2, h3⟩ := hp.1 bl B l r hB hr hl
    refine ⟨h0, ?_, h2, ?_⟩
    · intro w hw
      have : w.key ∈ r.unview.ws.map WEntry.key := List.mem_map_of_mem hw
      rw [NRec.unview_keys] at this
      obtain ⟨w0, hw0, he⟩ := List.mem_map.1 this
      rw [← he]; exact h1 w0 hw0
    · intro c hc
      obtain ⟨hcl, hcs⟩ := h3 c hc
      refine ⟨hcl, ?_⟩
      rw [unview_ns]; simpa using hcs
  · intro bl B' hB' hl
    obtain ⟨B, hB, rfl⟩ := rebase_bs_some hB'
    obtain ⟨h1, h2⟩ := hp.2.1 bl B hB hl
    refine ⟨fun k c hk => ?_, fun hrn => ?_⟩
    · obtain ⟨hcl, hcb⟩ := h1 k c hk
      refine ⟨hcl, ?_⟩
      rw [rebase_bs]; simpa using hcb
    · obtain ⟨rt, hrt, hrl⟩ := h2 hrn
      exact ⟨rt, nodeRootIn_unview hrt, hrl⟩
  · intro bl B' hB'
    obtain ⟨B, hB, rfl⟩ := rebase_bs_some hB'
    refine ⟨(hp.2.2.1 bl B hB).1, ?_⟩
    rw [unview_ns, (hp.2.2.1 bl B hB).2]; rfl
  · show ((X.rebase b).t.bs !! X.rl).isSome
    rw [rebase_bs]; simpa using hp.2.2.2.1
  · intro l hl
    have : (X.t.dead !! l).isSome := by simpa [WX.rebase, GMap.lookup_fmap] using hl
    exact hp.2.2.2.2 l this

theorem liveReach_rebase (X : WX) (b : Loc) (hr : liveReach X) : liveReach (X.rebase b) := by
  refine ⟨fun bl B' hB' hl => ?_, fun bl B' l r' hB' hr' hl => ?_⟩
  · obtain ⟨B, hB, rfl⟩ := rebase_bs_some hB'
    exact bktReach_rebase X b (hr.1 bl B hB hl)
  · obtain ⟨B, hB, rfl⟩ := rebase_bs_some hB'
    obtain ⟨r, hr0, rfl⟩ := unview_ns_some hr'
    obtain ⟨rt, hrt, hd⟩ := hr.2 bl B l r hB hr0 hl
    exact ⟨rt, nodeRootIn_unview hrt, descIn_unview hd⟩

theorem Src.unview_ne_stale {s : Src} (h1 : s ≠ .stale) (h2 : s ≠ .view) : s.unview ≠ .stale := by
  cases s <;> simp_all [Src.unview]

/-- **No live view slice, so nothing live goes stale** (`derefOK`, over disjoint objects). -/
theorem liveFresh_rebase (X : WX) (b : Loc) (hd : objsDisj X.t) (hc : derefOK X)
    (hf : liveFresh X) : liveFresh (X.rebase b) := by
  intro bl B' l r' hB' hr' hl
  obtain ⟨B, hB, rfl⟩ := rebase_bs_some hB'
  obtain ⟨r, hr, rfl⟩ := unview_ns_some hr'
  have hl' : l ∈ X.live := hl
  obtain ⟨h1, h2⟩ := hf bl B l r hB hr hl'
  have hv := hc l _ (objs_node X.t bl B l r hd hB hr) hl'
  simp only at hv
  obtain ⟨hvw, hvk⟩ := hv
  refine ⟨fun w hw => ?_, fun hne => ?_⟩
  · simp only [NRec.unview, WEntry.unview, List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact ⟨Src.unview_ne_stale (h1 w0 hw0).1 (hvw w0 hw0).1,
      Src.unview_ne_stale (h1 w0 hw0).2 (hvw w0 hw0).2⟩
  · exact Src.unview_ne_stale (h2 hne) hvk

/-! ## `allocate`'s premises kept -/

/-- **`dereference`, then the re-base, keep the premises** (`Inv/Ctx`'s
`derefRel_rebase_derefPre`, with the objects disjoint). -/
theorem derefRel_rebase_derefPre' (X Xd : WX) (b : Loc) (h : derefRel X Xd) (hd : objsDisj X.t)
    (hp : derefPre X) (hf : liveFresh X) (hr : liveReach X) :
    derefPre (Xd.rebase b) ∧ liveFresh (Xd.rebase b) ∧ liveReach (Xd.rebase b) := by
  have hs := h.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨derefPre_rebase Xd b (derefPre_step hs hp), ?_,
    liveReach_rebase Xd b (liveReach_step hs hr)⟩
  exact liveFresh_rebase Xd b (objsDisj_step hs hd) h.1 (liveFresh_step hs hf)

/-- **A successful `allocate` keeps its premises** (`Inv/Ctx`'s `allocRes_derefPre`, with the
objects disjoint). -/
theorem allocRes_derefPre' (X X' : WX) (fl fl' : FLPg) (txid : w64) (count : Nat) (p : Loc)
    (id : w64) (h : allocRes X X' fl fl' txid count p id) (hd : objsDisj X.t) (hp : derefPre X)
    (hf : liveFresh X) (hr : liveReach X) : derefPre X' ∧ liveFresh X' ∧ liveReach X' := by
  obtain ⟨-, -, Xr, hXr, hX'⟩ := h
  have hR : derefPre Xr ∧ liveFresh Xr ∧ liveReach Xr := by
    rcases hXr with rfl | ⟨Xd, b, hdr, rfl⟩
    · exact ⟨hp, hf, hr⟩
    · exact derefRel_rebase_derefPre' X Xd b hdr hd hp hf hr
  obtain ⟨h1, h2, h3⟩ := hR
  rcases hX' with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;>
    exact ⟨derefPre_addPage _ _ _ _ _ h1, liveFresh_addPage _ _ _ _ _ h2,
      liveReach_addPage _ _ _ _ _ h3⟩

end allocDeref

end bbolt
end EtcdGrove
end Perennial
