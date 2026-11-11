/-
`Bucket.spill`'s root loop (U9x2, `notes/bbolt-proof-plan.md`): **the root bucket's leaf put,
the pure tree facts** (`BktLoopPureRPut.rinv_put'`'s). What `Cursor.node`'s materializations
(`matGrow`) keep of the whole writer (`matGrow_frame`); a node record changed (`setNode`) whose
leaf keeps its kind changes the logical tree at its positions only (`setNode_ltree`,
`setNode_blocks`), so a finite tree stays one (`ltIs_leafRep`); a found bucket entry replaced in a
sorted leaf replaces its value in the bucket entries (`bktOf_putAt`), and in the root bucket's when
the leaf's blocks are those holding the key (`rootEnts_putAt`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureMat
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailPureG
public import Proof.go_etcd_io.bbolt.Write.DataWalk
public import Proof.go_etcd_io.bbolt.Write.Data
public import Proof.go_etcd_io.bbolt.Write.NodeEnts

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section rputT
variable [GooseExts]

/-! ## What materializations keep -/

/-- **What `matGrow` keeps of the whole writer.** -/
theorem matGrow_frame {X X' : WX} {bl : Loc} (h : matGrow X X' bl) :
    X'.rl = X.rl ∧ X'.liveB = X.liveB ∧ X'.t.bufs = X.t.bufs ∧ X'.t.pm = X.t.pm ∧
    X'.t.mv = X.t.mv ∧ X'.v = X.v ∧ (∀ c, c ≠ bl → X'.t.bs !! c = X.t.bs !! c) ∧
    (∀ B, X.t.bs !! bl = some B → ∃ B', X'.t.bs !! bl = some B' ∧ B'.bm = B.bm ∧
      B'.bv.buckets' = B.bv.buckets' ∧ B'.ib = B.ib) ∧
    (∀ x ∈ X.live, x ∈ X'.live) ∧ X'.fuel = X.fuel := by
  induction h with
  | refl => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl,
      fun B hB => ⟨B, hB, rfl, rfl, rfl⟩, fun _ h => h, rfl⟩
  | step X Y Z bl l pgid parent hadd _ _ ih =>
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ := ih
    obtain ⟨B, pa, pg, r, ns', bv', hB, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, 
      hcase, hX'⟩ := hadd
    subst hX'
    refine ⟨i1, i2, i3, i4, i5, i6, fun c hc => ?_, fun B0 hB0 => ?_, fun x hx => ?_, ?_⟩
    · rw [i7 c hc]; exact GMap.lookup_insert_ne _ _ (Ne.symm hc)
    · rw [hB] at hB0; cases hB0
      obtain ⟨B', hB', e1, e2, e3⟩ := i8 _ (GMap.lookup_insert _ _ _)
      refine ⟨B', hB', e1, ?_, e3⟩
      rw [e2]
      rcases hcase with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> rfl
    · exact i9 x (mem_insert_unit.2 (Or.inr hx))
    · rw [i10]
      unfold WX.fuel
      show X.v.pages.size + (X.t.bs.insert bl _).size + 1 = X.v.pages.size + X.t.bs.size + 1
      rw [GMap.map_size_insert_Some _ _ _ _ hB]

/-! ## A finite tree through a change of leaves' entries -/

section rep
variable (L L' : LTree) (bl : Loc)
  (h : ∀ q, L' bl q = L bl q ∨ ∃ ws ws', L bl q = some (true, ws) ∧ L' bl q = some (true, ws'))
include h

mutual
/-- **A tree survives a change of leaves' entries.** -/
theorem ltIs_leafRep : ∀ (t : RTree), ltIs L bl t → ∃ t', ltIs L' bl t' ∧ t'.pid = t.pid ∧
    t'.ht = t.ht ∧ ∀ d, t'.dps d = t.dps d
  | .mk p true ws cs, ht => by
    simp only [ltIs] at ht
    obtain ⟨hL, rfl⟩ := ht
    rcases h p with e | ⟨ws0, ws', -, h1⟩
    · exact ⟨.mk p true ws [], ⟨by rw [e]; exact hL, rfl⟩, rfl, rfl, fun d => rfl⟩
    · exact ⟨.mk p true ws' [], ⟨h1, rfl⟩, rfl, rfl, fun d => rfl⟩
  | .mk p false ws cs, ht => by
    simp only [ltIs] at ht
    obtain ⟨hL, hcs⟩ := ht
    have hL' : L' bl p = some (false, ws) := by
      rcases h p with e | ⟨ws0, ws1, h0, -⟩
      · rw [e]; exact hL
      · rw [hL] at h0; cases h0
    obtain ⟨cs', hcs', hh, hd⟩ := ltIsL_leafRep ws cs hcs
    exact ⟨.mk p false ws cs', ⟨hL', hcs'⟩, rfl, by simp only [RTree.ht]; exact hh,
      fun d => by simp only [RTree.dps]; exact hd (d + 1)⟩
theorem ltIsL_leafRep : ∀ (ws : List WEntry) (cs : List RTree), ltIsL L bl ws cs →
    ∃ cs', ltIsL L' bl ws cs' ∧ RTree.htL cs' = RTree.htL cs ∧
      ∀ d, RTree.dpsL d cs' = RTree.dpsL d cs
  | [], [], _ => ⟨[], trivial, rfl, fun _ => rfl⟩
  | w :: ws, t :: ts, hl => by
    simp only [ltIsL] at hl
    obtain ⟨hp, ht, hts⟩ := hl
    obtain ⟨t', ht', hpid, hh, hd⟩ := ltIs_leafRep t ht
    obtain ⟨ts', hts', hh', hd'⟩ := ltIsL_leafRep ws ts hts
    refine ⟨t' :: ts', ⟨by rw [hpid, hp], ht', hts'⟩, ?_, fun d => ?_⟩
    · simp only [RTree.htL]; rw [hh, hh']
    · simp only [RTree.dpsL]; rw [hd, hd']
  | [], _ :: _, hl => by simp only [ltIsL] at hl
  | _ :: _, [], hl => by simp only [ltIsL] at hl
end

end rep

/-! ## A node's record changed -/

theorem setNode_rl (X : WX) (bl l : Loc) (r : NRec) : (X.setNode bl l r).rl = X.rl := by
  unfold WX.setNode; split <;> rfl

theorem setNode_v (X : WX) (bl l : Loc) (r : NRec) : (X.setNode bl l r).v = X.v := by
  unfold WX.setNode; split <;> rfl

theorem setNode_liveB (X : WX) (bl l : Loc) (r : NRec) : (X.setNode bl l r).liveB = X.liveB := by
  unfold WX.setNode; split <;> rfl

theorem setNode_live (X : WX) (bl l : Loc) (r : NRec) : (X.setNode bl l r).live = X.live := by
  unfold WX.setNode; split <;> rfl

theorem setNode_pm (X : WX) (bl l : Loc) (r : NRec) : (X.setNode bl l r).t.pm = X.t.pm := by
  unfold WX.setNode; split <;> rfl

theorem setNode_mv (X : WX) (bl l : Loc) (r : NRec) : (X.setNode bl l r).t.mv = X.t.mv := by
  unfold WX.setNode; split <;> rfl

theorem setNode_bufs (X : WX) (bl l : Loc) (r : NRec) : (X.setNode bl l r).t.bufs = X.t.bufs := by
  unfold WX.setNode; split <;> rfl

variable {X : WX} {bl l : Loc} {B : BRec} {r r' : NRec}

theorem setNode_bs_other (hB : X.t.bs !! bl = some B) {c : Loc} (hc : c ≠ bl) :
    (X.setNode bl l r').t.bs !! c = X.t.bs !! c := by
  rw [setNode_eqQ hB]; exact GMap.lookup_insert_ne _ _ (Ne.symm hc)

theorem setNode_bs_self (hB : X.t.bs !! bl = some B) :
    (X.setNode bl l r').t.bs !! bl = some { B with ns := B.ns.insert l r' } := by
  rw [setNode_eqQ hB]; exact GMap.lookup_insert _ _ _

theorem setNode_fuel (hB : X.t.bs !! bl = some B) : (X.setNode bl l r').fuel = X.fuel := by
  rw [setNode_eqQ hB]
  unfold WX.fuel
  show X.v.pages.size + (X.t.bs.insert bl _).size + 1 = X.v.pages.size + X.t.bs.size + 1
  rw [GMap.map_size_insert_Some _ _ _ _ hB]

theorem setNode_rootPid (hB : X.t.bs !! bl = some B) (c : Loc) :
    (X.setNode bl l r').rootPid c = X.rootPid c := by
  unfold WX.rootPid
  by_cases hc : c = bl
  · subst hc; rw [setNode_bs_self hB, hB]; rfl
  · rw [setNode_bs_other hB hc]

/-- **The logical tree after a record change** keeping the node's kind. -/
theorem setNode_ltree (hB : X.t.bs !! bl = some B) (hlf : r'.nv.isLeaf' = r.nv.isLeaf')
    (bl' : Loc) (p : w64) :
    ltree (X.setNode bl l r') bl' p =
      if bl' = bl ∧ resolve B p = some l then some (r.nv.isLeaf', r'.ws) else ltree X bl' p := by
  by_cases hb : bl' = bl
  · subst hb
    unfold ltree
    rw [setNode_bs_self hB, hB]
    have hres : resolve { B with ns := B.ns.insert l r' } p = resolve B p := rfl
    have hwp : wpageAt (X.setNode bl' l r').v { B with ns := B.ns.insert l r' } p =
      wpageAt X.v B p := by rw [setNode_v]; rfl
    simp only [hres, hwp]
    cases hp : resolve B p with
    | none => simp
    | some m =>
      by_cases hm : m = l
      · subst hm; simp [hlf]
      · simp only [Option.some.injEq, hm, and_false, ↓reduceIte]
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hm)]
  · rw [if_neg (fun h => hb h.1)]
    unfold ltree
    rw [setNode_bs_other hB hb, setNode_v]

/-- The blocks of the walk after a leaf's record change: `X`'s, with `l`'s entries replaced. -/
theorem setNode_blocks (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r)
    (hleaf : r.nv.isLeaf' = true) (hlf : r'.nv.isLeaf' = true) (c : Loc) :
    Write.lleavesB (ltree (X.setNode bl l r')) c (X.setNode bl l r').fuel
        ((X.setNode bl l r').rootPid c) (none, none) =
      (Write.lleavesB (ltree X) c X.fuel (X.rootPid c) (none, none)).map
        fun x => if decide (c = bl ∧ resolve B x.1 = some l) then (x.1, x.2.1, r'.ws) else x := by
  rw [setNode_fuel hB, setNode_rootPid hB]
  apply Write.lleavesB_replace (ltree X) _ c (fun p => decide (c = bl ∧ resolve B p = some l))
  · intro p
    rw [setNode_ltree hB (hlf.trans hleaf.symm), hleaf]
    simp
  · intro p hp
    simp only [decide_eq_true_eq] at hp
    obtain ⟨rfl, hp⟩ := hp
    refine ⟨r.ws, ?_⟩
    unfold ltree; simp [hB, hp, hr, hleaf]

/-! ## A found bucket entry's value replaced -/

theorem wsPw_key_inj {ws : List WEntry} (h : Write.wsPw ws) {a b : WEntry} (ha : a ∈ ws)
    (hb : b ∈ ws) (e : a.key = b.key) : a = b := by
  induction ws with
  | nil => cases ha
  | cons c t ih =>
    unfold Write.wsPw at h
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · rfl
      · have := h.1 b hb'; rw [e] at this; exact absurd this (go.goStringLt_irrefl _)
    · rcases List.mem_cons.1 hb with rfl | hb'
      · have := h.1 a ha'; rw [← e] at this; exact absurd this (go.goStringLt_irrefl _)
      · exact ih h.2 ha' hb'

/-- The bucket entries' value at key `k` replaced by `v`. -/
def repVal (k v : List w8) (x : GoString × List w8) : GoString × List w8 :=
  if x.1 = k then (k, v) else x

theorem filterMap_bktOf_nokey {ws : List WEntry} {k : List w8} (h : ∀ w ∈ ws, w.key ≠ k)
    (v : List w8) : (ws.filterMap Write.bktOf).map (repVal k v) = ws.filterMap Write.bktOf := by
  conv => rhs; rw [← List.map_id (ws.filterMap Write.bktOf)]
  apply List.map_congr_left
  intro x hx
  obtain ⟨w, hw, hwx⟩ := List.mem_filterMap.1 hx
  unfold repVal
  rw [if_neg (by rw [Write.bktOf_key w x hwx]; exact h w hw)]; rfl

theorem bktOf_set {ws : List WEntry} {k : List w8} {e : WEntry} (hpw : Write.wsPw ws)
    (hbk : ∀ w ∈ ws, w.key = k → isBktFlag w.flags) (hek : e.key = k) (hef : isBktFlag e.flags) :
    ∀ i (hi : i < ws.length), ws[i].key = k →
      (ws.set i e).filterMap Write.bktOf = (ws.filterMap Write.bktOf).map (repVal k e.value) := by
  induction ws with
  | nil => intro i hi; cases hi
  | cons a t ih =>
    have hpw' := hpw
    unfold Write.wsPw at hpw'
    rw [List.pairwise_cons] at hpw'
    intro i hi hki
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hki
      have hnt : ∀ w ∈ t, w.key ≠ k := by
        intro w hw e'
        have := hpw'.1 w hw
        rw [hki, e'] at this
        exact go.goStringLt_irrefl _ this
      simp only [List.set_cons_zero, List.filterMap_cons]
      have h1 : Write.bktOf e = some (k, e.value) := by
        unfold Write.bktOf; rw [if_pos (decide_eq_true hef), hek]
      have h2 : Write.bktOf a = some (k, a.value) := by
        unfold Write.bktOf; rw [if_pos (decide_eq_true (hbk a (List.mem_cons_self) hki)), hki]
      rw [h1, h2, List.map_cons, filterMap_bktOf_nokey hnt]
      unfold repVal; simp
    | succ j =>
      simp only [List.length_cons] at hi
      simp only [List.getElem_cons_succ] at hki
      have hak : a.key ≠ k := by
        intro e'
        have := hpw'.1 t[j] (List.getElem_mem _)
        rw [e', hki] at this
        exact go.goStringLt_irrefl _ this
      simp only [List.set_cons_succ, List.filterMap_cons]
      rw [ih hpw'.2 (fun w hw => hbk w (List.mem_cons_of_mem _ hw)) j (by omega) hki]
      cases hba : Write.bktOf a with
      | none => rfl
      | some x =>
        simp only [List.map_cons]
        unfold repVal
        rw [if_neg (by rw [Write.bktOf_key a x hba]; exact hak)]

/-- **A found bucket entry replaced** (`wsPutAt` at its key) replaces its value. -/
theorem bktOf_putAt {ws : List WEntry} {k : List w8} {e : WEntry} (hpw : Write.wsPw ws)
    (hf : wsFound ws k) (hbk : ∀ w ∈ ws, w.key = k → isBktFlag w.flags) (hek : e.key = k)
    (hef : isBktFlag e.flags) :
    (wsPutAt ws k e).filterMap Write.bktOf = (ws.filterMap Write.bktOf).map (repVal k e.value) := by
  obtain ⟨hi, hki⟩ := (Write.wsFound_iff ws k).1 hf
  rw [Write.wsPutAt_eq, if_pos hf]
  refine bktOf_set hpw hbk hek hef _ hi ?_
  unfold wKey at hki; rw [List.getElem?_eq_getElem hi] at hki; simpa using hki

/-- **The root bucket's entries after the put** of a found bucket entry into the leaf `l`, the
walk's blocks at `l`'s positions exactly those holding the key. -/
theorem rootEnts_putAt (hB : X.t.bs !! X.rl = some B) (hr : B.ns !! l = some r)
    (hleaf : r.nv.isLeaf' = true) (hlf : r'.nv.isLeaf' = true) {k : List w8} {e : WEntry}
    (hws : r'.ws = wsPutAt r.ws k e) (hpw : Write.wsPw r.ws) (hf : wsFound r.ws k)
    (hbk : ∀ w ∈ r.ws, w.key = k → isBktFlag w.flags) (hek : e.key = k)
    (hef : isBktFlag e.flags)
    (hsel : ∀ x ∈ Write.lleavesB (ltree X) X.rl X.fuel (X.rootPid X.rl) (none, none),
      resolve B x.1 ≠ some l → ∀ w ∈ x.2.2, w.key ≠ k) :
    rootEnts (X.setNode X.rl l r') = (rootEnts X).map (repVal k e.value) := by
  rw [Write.rootEnts_blocks, Write.rootEnts_blocks, setNode_rl, setNode_blocks hB hr hleaf hlf,
    List.flatMap_map, List.map_flatMap]
  apply Write.fm_congr
  intro x hx
  by_cases hs : resolve B x.1 = some l
  · rw [if_pos (decide_eq_true ⟨rfl, hs⟩), Write.block_ws X _ l B r hB hr _ _ _ x hx hs]
    simp only
    rw [hws]
    exact bktOf_putAt hpw hf hbk hek hef
  · rw [if_neg (by simp [hs])]
    exact (filterMap_bktOf_nokey (hsel x hx hs) _).symm

end rputT

end Spill

end bbolt
end EtcdGrove
end Perennial
