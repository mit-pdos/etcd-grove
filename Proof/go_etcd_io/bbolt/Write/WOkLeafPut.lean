/-
**What `Bucket.Put` and `Bucket.Delete` give back to `boltTx`** (U7i, `notes/bbolt-proof-plan.md`),
pure: after `Cursor.node`'s materializations (`matGrow X X3 b`) and `node.put`/`node.del` on the
leaf `l` of the handle's bucket `b` (a bucket of the root bucket, not the root), the records `X4`
are well-formed (`Write/WOkLeaf`), hold the data with the entry put/deleted (`wtxData_put'`,
`wtxData_del'`), keep the generations, the carried facts (`wrFacts`: `liveReach` across
materializations, `liveReach_nodeAdded`, as `Spill/BktLoopPureMat.spG_nodeAdded`'s, and the leaf's
update, `liveReach_setNode`) and what the exclusive part keeps (`XclKeep`: `flViewU`,
`Write/CovUMat`, `Write/FlViewU`). `putPost`, `delPost`, `delPostNF` (the key not found).
-/
module

public import Proof.go_etcd_io.bbolt.Write.WOkLeaf
public import Proof.go_etcd_io.bbolt.Write.CovUMat
public import Proof.go_etcd_io.bbolt.Write.FlViewU
public import Proof.go_etcd_io.bbolt.Write.Data
public import Proof.go_etcd_io.bbolt.Write.Retarget
public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsGens

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wokput
variable [GooseExts]

/-! ## What materializations keep -/

theorem mem_insert_unit' {m : GMap Loc Unit} {a b : Loc} : a ∈ m.insert b () ↔ a = b ∨ a ∈ m := by
  show ((m.insert b ()) !! a).isSome ↔ a = b ∨ (m !! a).isSome
  by_cases h : a = b
  · subst h; rw [GMap.lookup_insert]; simp
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]; simp [h]

/-- **What `matGrow` keeps**: the handles, the root bucket, the view, the transaction's struct
and meta copy, the live buckets, and every bucket's cache of nested buckets. -/
theorem matGrow_keepW {X X' : WX} {bl : Loc} (h : matGrow X X' bl) :
    X'.handles = X.handles ∧ X'.rl = X.rl ∧ X'.v = X.v ∧ X'.t.t = X.t.t ∧ X'.t.mv = X.t.mv ∧
      X'.liveB = X.liveB ∧
      (∀ c B, X.t.bs !! c = some B → ∃ B', X'.t.bs !! c = some B' ∧ B'.bm = B.bm) ∧
      (∀ c B', X'.t.bs !! c = some B' → ∃ B, X.t.bs !! c = some B ∧ B'.bm = B.bm) := by
  induction h with
  | refl => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun c B h => ⟨B, h, rfl⟩, fun c B h => ⟨B, h, rfl⟩⟩
  | step X Y Z bl l pgid parent hadd _ _ ih =>
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ih
    obtain ⟨B, pa, pg, r, ns', bv', hB, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, hX'⟩ := hadd
    subst hX'
    refine ⟨i1, i2, i3, i4, i5, i6, fun c C hC => ?_, fun c C hC => ?_⟩
    · by_cases e : c = bl
      · subst e; rw [hB] at hC; cases hC
        obtain ⟨B', h1, h2⟩ := i7 c _
          (GMap.lookup_insert X.t.bs c { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' })
        exact ⟨B', h1, h2⟩
      · exact i7 c C (show (X.t.bs.insert bl { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' }) !! c = _
          by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hC)
    · obtain ⟨C0, hC0, e0⟩ := i8 c C hC
      by_cases e : c = bl
      · subst e
        rw [GMap.lookup_insert] at hC0; cases hC0
        exact ⟨B, hB, e0⟩
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hC0
        exact ⟨C0, hC0, e0⟩

theorem bktLoc_matGrow {X X' : WX} {bl : Loc} (h : matGrow X X' bl) (n : GoString) :
    bktLoc X' n = bktLoc X n := by
  obtain ⟨-, hrl, -, -, -, -, h7, h8⟩ := matGrow_keepW h
  unfold bktLoc
  rw [hrl]
  cases hR : X.t.bs !! X.rl with
  | none =>
    cases hR' : X'.t.bs !! X.rl with
    | none => rfl
    | some R' =>
      obtain ⟨R, hR0, -⟩ := h8 _ R' hR'
      rw [hR] at hR0; cases hR0
  | some R =>
    obtain ⟨R', hR', e⟩ := h7 _ R hR
    rw [hR']; simp only [Option.bind_some]; rw [e]

/-! ## `liveReach` -/

theorem nodeRootIn_par' {B B' : BRec}
    (h : ∀ x rx, B.ns !! x = some rx → ∃ rx', B'.ns !! x = some rx' ∧ rx'.nv.parent' = rx.nv.parent')
    {a rt : Loc} (hr : nodeRootIn B a rt) : nodeRootIn B' a rt := by
  induction hr with
  | top n r hn hp =>
    obtain ⟨r', hr', e⟩ := h n r hn
    exact nodeRootIn.top n r' hr' (by rw [e]; exact hp)
  | up n rt r hn hp _ ih =>
    obtain ⟨r', hr', e⟩ := h n r hn
    refine nodeRootIn.up n rt r' hr' (by rw [e]; exact hp) ?_
    rw [e]; exact ih

theorem descIn_grow' {B B' : BRec}
    (hk : ∀ x rx, B.ns !! x = some rx → ∃ rx', B'.ns !! x = some rx' ∧ ∀ c ∈ rx.cs, c ∈ rx'.cs)
    {a d : Loc} (h : descIn B a d) : descIn B' a d := by
  induction h with
  | self x => exact descIn.self x
  | child a c d ra ha hc _ ih =>
    obtain ⟨ra', ha', hcs⟩ := hk a ra ha
    exact descIn.child a c d ra' ha' (hcs c hc) ih

theorem descIn_snoc' {B : BRec} {a b c : Loc} {r : NRec} (h : descIn B a b)
    (hr : B.ns !! b = some r) (hc : c ∈ r.cs) : descIn B a c := by
  induction h with
  | self n => exact descIn.child n c c r hr hc (descIn.self c)
  | child n c' d r' hr' hc' _ ih => exact descIn.child n c' c r' hr' hc' (ih hr)

theorem bktReach_bm' {X Y : WX} (hrl : Y.rl = X.rl)
    (hbm : ∀ bl B, X.t.bs !! bl = some B → ∃ B', Y.t.bs !! bl = some B' ∧ B'.bm = B.bm)
    {c : Loc} (h : bktReach X c) : bktReach Y c := by
  induction h with
  | root => rw [← hrl]; exact bktReach.root
  | child bl c B n hB hn _ ih =>
    obtain ⟨B', hB', e⟩ := hbm bl B hB
    exact bktReach.child bl c B' n hB' (by rw [e]; exact hn) ih

/-- A clean bucket has no node at `null` (its node's page id would cache `null`). -/
theorem ns_null_none {v : View} {hwm : Nat} {bl : Loc} {B : BRec} (hc : bktClean v hwm bl B) :
    B.ns !! null = none := by
  cases h : B.ns !! null with
  | none => rfl
  | some r =>
    exfalso
    have h8 := (hc.2.2.2.2.2.2.2.1 null r h).2.2.2.2.2.2.2.1
    exact (hc.2.2.2.2.1 _ _ h8).1 rfl

/-- **A materialization keeps `liveReach`** (`Spill/BktLoopPureMat.spG_nodeAdded`'s argument). -/
theorem liveReach_nodeAdded {X Y : WX} {bl l : Loc} {pgid : w64} {parent : Loc}
    (hadd : nodeAdded X Y bl l pgid parent) (hpos : matPos X bl pgid parent) (hok : wOK X)
    (hr : liveReach X) : liveReach Y := by
  obtain ⟨rB, rN⟩ := hr
  obtain ⟨B, pa, pg, r, ns', bv', hB, -, -, hl0, hlo, -, hpar, -, -, -, -, hrcs, -, -, -, -, -,
    -, -, -, hcase, hX'⟩ := hadd
  have hlo' : X.t.objs !! l = none := by simpa using hlo
  have hpos' : (parent = null ∧ B.bv.rootNode' = null ∧ pgid = B.ib.root') ∨
      ∃ i, pagePosAt B parent i pgid := by
    obtain ⟨B', hB', hp⟩ := hpos; rw [hB] at hB'; cases hB'; exact hp
  have hfresh : ∀ c C, X.t.bs !! c = some C → C.ns !! l = none := objs_none X.t l hlo'
  have hcl := wOK_bktClean X hok bl B hB
  have hlv : ∀ x rx, B.ns !! x = some rx → x ∈ X.live :=
    fun x rx h => wOK_nsLive X hok bl B x rx hB h
  subst hX'
  have hbs : ∀ c C, (X.t.bs.insert bl { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' }) !! c
      = some C → (bl = c ∧ C = { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' }) ∨
        (c ≠ bl ∧ X.t.bs !! c = some C) := by
    intro c C hc
    by_cases e : c = bl
    · subst e; rw [GMap.lookup_insert] at hc; cases hc; exact Or.inl ⟨rfl, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hc; exact Or.inr ⟨e, hc⟩
  have hold : ∀ x rx, B.ns !! x = some rx → ∃ rx', ns' !! x = some rx' ∧
      rx'.nv.parent' = rx.nv.parent' ∧ ∀ c ∈ rx.cs, c ∈ rx'.cs := by
    intro x rx hx
    have hxl : x ≠ l := by intro e; subst e; rw [hfresh bl B hB] at hx; cases hx
    rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', hrp, -, hcs', -, -, -, -, -, hnv, rfl⟩
    · exact ⟨rx, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hxl)]; exact hx, rfl, fun c h => h⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxl)]
      by_cases hxp : x = parent
      · subst hxp; rw [hrp] at hx; cases hx
        refine ⟨rp', GMap.lookup_insert _ _ _, by rw [hnv], fun c h => ?_⟩
        rw [hcs']; exact List.mem_append_left _ h
      · exact ⟨rx, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hxp)]; exact hx, rfl, fun c h => h⟩
  refine ⟨?_, ?_⟩
  · -- buckets reached
    intro c C hC hcl'
    have hc0 : ∃ C0, X.t.bs !! c = some C0 := by
      rcases hbs c C hC with ⟨rfl, -⟩ | ⟨-, hC'⟩
      · exact ⟨B, hB⟩
      · exact ⟨C, hC'⟩
    obtain ⟨C0, hC0⟩ := hc0
    refine bktReach_bm' (X := X) (by rfl) (fun b Bb hb => ?_) (rB c C0 hC0 hcl')
    by_cases e : b = bl
    · subst e; rw [hB] at hb; cases hb
      exact ⟨_, GMap.lookup_insert _ _ _, rfl⟩
    · exact ⟨Bb, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hb, rfl⟩
  · -- nodes reached
    intro c C x rx hC hx hxl
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hne, hC'⟩
    · rcases hcase with ⟨hp0, hbv, rfl⟩ | ⟨hp0, hbv, rp, rp', hrp, -, hcs', -, -, -, -, -, hnv, rfl⟩
      · -- the bucket's new root node: no old nodes
        have hrn0 : B.bv.rootNode' = null := by
          rcases hpos' with ⟨-, h, -⟩ | ⟨i, r0, -, hr0, -⟩
          · exact h
          · rw [hp0, ns_null_none hcl] at hr0; cases hr0
        have hns0 := (hcl.2.2.1 hrn0).1
        have hxl : x = l := by
          by_cases e : x = l
          · exact e
          · rw [GMap.lookup_insert_ne _ _ (Ne.symm e), hns0] at hx; cases hx
        subst hxl
        refine ⟨x, ?_, descIn.self x⟩
        rw [hbv]
        exact nodeRootIn.top x r (GMap.lookup_insert _ _ _) (by rw [hpar, hp0])
      · have hrt : ∀ rt, nodeRootIn B B.bv.rootNode' rt →
            nodeRootIn { B with nm := B.nm.insert pgid l, ns := (B.ns.insert parent rp').insert l r, bv := bv' } bv'.rootNode' rt := by
          intro rt h
          rw [hbv]
          exact nodeRootIn_par' (fun y ry hy => by
            obtain ⟨ry', h1, h2, -⟩ := hold y ry hy; exact ⟨ry', h1, h2⟩) h
        have hgrow : ∀ a d, descIn B a d → descIn { B with nm := B.nm.insert pgid l, ns := (B.ns.insert parent rp').insert l r, bv := bv' } a d :=
          fun a d h => descIn_grow' (fun y ry hy => by
            obtain ⟨ry', h1, -, h3⟩ := hold y ry hy; exact ⟨ry', h1, h3⟩) h
        by_cases e : x = l
        · subst e
          obtain ⟨rt, h1, h2⟩ := rN bl B parent rp hB hrp (hlv parent rp hrp)
          refine ⟨rt, hrt rt h1, descIn_snoc' (hgrow rt parent h2) (r := rp') ?_ ?_⟩
          · have hpl : parent ≠ x := by intro e; rw [e, hfresh bl B hB] at hrp; cases hrp
            show ((B.ns.insert parent rp').insert x r) !! parent = some rp'
            rw [GMap.lookup_insert_ne _ _ (Ne.symm hpl), GMap.lookup_insert]
          · rw [hcs']; exact List.mem_append_right _ (List.mem_singleton_self _)
        · have hx0 : ∃ rx0, B.ns !! x = some rx0 := by
            rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hx
            by_cases hxp : x = parent
            · exact ⟨rp, by rw [hxp]; exact hrp⟩
            · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxp)] at hx; exact ⟨rx, hx⟩
          obtain ⟨rx0, hrx0⟩ := hx0
          obtain ⟨rt, h1, h2⟩ := rN bl B x rx0 hB hrx0 (hlv x rx0 hrx0)
          exact ⟨rt, hrt rt h1, hgrow rt x h2⟩
    · have hxl' : x ∈ X.live := by
        rcases mem_insert_unit'.1 hxl with e | h
        · subst e; rw [hfresh c C hC'] at hx; cases hx
        · exact h
      exact rN c C x rx hC' hx hxl'

/-- **Materializations keep `liveReach`** (from `wOK` at the start). -/
theorem liveReach_matGrow {X X' : WX} {bl : Loc} (h : matGrow X X' bl) (hok : wOK X)
    (hr : liveReach X) : liveReach X' := by
  induction h with
  | refl => exact hr
  | step X Y Z bl l pgid parent hadd hpos _ ih =>
    exact ih (wOK_nodeAdded X Y bl l pgid parent hok hadd hpos)
      (liveReach_nodeAdded hadd hpos hok hr)

/-- **A node's record replaced, its parent and children kept, keeps `liveReach`.** -/
theorem liveReach_setNode (X : WX) (bl l : Loc) (B : BRec) (r r' : NRec)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) (hp : r'.nv.parent' = r.nv.parent')
    (hcs : r'.cs = r.cs) (h : liveReach X) : liveReach (X.setNode bl l r') := by
  obtain ⟨rB, rN⟩ := h
  rw [setNode_eqT X bl l B r' hB]
  let B' : BRec := { B with ns := B.ns.insert l r' }
  have hbs : ∀ c C, (X.t.bs.insert bl B') !! c = some C →
      (c = bl ∧ C = B') ∨ (c ≠ bl ∧ X.t.bs !! c = some C) := by
    intro c C h
    by_cases e : c = bl
    · subst e; rw [GMap.lookup_insert] at h; cases h; exact Or.inl ⟨rfl, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h; exact Or.inr ⟨e, h⟩
  have hold : ∀ x rx, B.ns !! x = some rx → ∃ rx', B'.ns !! x = some rx' ∧
      rx'.nv.parent' = rx.nv.parent' ∧ ∀ c ∈ rx.cs, c ∈ rx'.cs := by
    intro x rx hx
    by_cases e : x = l
    · subst e; rw [hr] at hx; cases hx
      exact ⟨r', GMap.lookup_insert _ _ _, hp, fun c h => by rw [hcs]; exact h⟩
    · refine ⟨rx, ?_, rfl, fun c h => h⟩
      show (B.ns.insert l r') !! x = _
      rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hx
  refine ⟨fun c C hC hcl' => ?_, fun c C x rx hC hx hxl => ?_⟩
  · have hc0 : ∃ C0, X.t.bs !! c = some C0 := by
      rcases hbs c C hC with ⟨rfl, -⟩ | ⟨-, hC'⟩
      · exact ⟨B, hB⟩
      · exact ⟨C, hC'⟩
    obtain ⟨C0, hC0⟩ := hc0
    refine bktReach_bm' (X := X) (by rfl) (fun b Bb hb => ?_) (rB c C0 hC0 hcl')
    by_cases e : b = bl
    · subst e; rw [hB] at hb; cases hb
      exact ⟨_, show (X.t.bs.insert b B') !! b = _ from GMap.lookup_insert _ _ _, rfl⟩
    · exact ⟨Bb, show (X.t.bs.insert bl B') !! b = _ by
        rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hb, rfl⟩
  · rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨-, hC'⟩
    · have hx0 : ∃ rx0, B.ns !! x = some rx0 := by
        by_cases e : x = l
        · subst e; exact ⟨r, hr⟩
        · have h' : (B.ns.insert l r') !! x = some rx := hx
          rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h'; exact ⟨rx, h'⟩
      obtain ⟨rx0, hrx0⟩ := hx0
      obtain ⟨rt, h1, h2⟩ := rN c B x rx0 hB hrx0 hxl
      refine ⟨rt, ?_, descIn_grow' (fun y ry hy => by
        obtain ⟨ry', h1, -, h3⟩ := hold y ry hy; exact ⟨ry', h1, h3⟩) h2⟩
      exact nodeRootIn_par' (fun y ry hy => by
        obtain ⟨ry', h1, h2, -⟩ := hold y ry hy; exact ⟨ry', h1, h2⟩) h1
    · exact rN c C x rx hC' hx hxl

/-! ## The posts -/

/-- `wrFacts`' third clause and `bktLoc`: the handle's bucket is not the root. -/
theorem bktLoc_ne_root (X : WX) (hwr : wrFacts X) (n : GoString) (b : Loc)
    (hb : bktLoc X n = some b) : b ≠ X.rl := by
  unfold bktLoc at hb
  cases hR : X.t.bs !! X.rl with
  | none => rw [hR] at hb; cases hb
  | some R =>
    rw [hR] at hb
    exact hwr.2.2 R hR n b hb

/-- **What `Put` and `Delete` keep beside their records' update**: the materializations' and the
leaf's facts (handles, root, view, struct, meta copy, live buckets, root bucket's cache) from `X` to
`X4 = X3.setNode b l r'`. -/
theorem post_common (T : TxView) (X X3 : WX) (b l : Loc) (B3 : BRec) (rl r' : NRec)
    (hok : wOK X) (hgens : gensOK T X) (hwr : wrFacts X) (hmg : matGrow X X3 b)
    (hB3 : X3.t.bs !! b = some B3) (hrl : B3.ns !! l = some rl) (hlf : rl.nv.isLeaf' = true)
    (hroot : b ≠ X.rl) (hsh : sameShapeU rl r') :
    gensOK T (X3.setNode b l r') ∧ wrFacts (X3.setNode b l r') ∧
      XclKeep X (X3.setNode b l r') ∧ (X3.setNode b l r').rl = X.rl := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := matGrow_keepW hmg
  obtain ⟨e1, e2, e3, e4, e5, e6, e8, e9, e10, e11⟩ := hsh
  have hX4 := setNode_eqT X3 b l B3 r' hB3
  have hh4 : (X3.setNode b l r').handles = X.handles := by rw [hX4]; exact k1
  have hrl4 : (X3.setNode b l r').rl = X.rl := by rw [hX4]; exact k2
  have hbm4 : ∀ c C, X.t.bs !! c = some C → ∃ C', (X3.setNode b l r').t.bs !! c = some C' ∧
      C'.bm = C.bm := by
    intro c C hC
    obtain ⟨C3, hC3, e⟩ := k7 c C hC
    rw [hX4]
    by_cases ec : c = b
    · subst ec; rw [hB3] at hC3; cases hC3
      exact ⟨_, GMap.lookup_insert _ _ _, e⟩
    · exact ⟨C3, by show (X3.t.bs.insert b _) !! c = _; rw [GMap.lookup_insert_ne _ _ (Ne.symm ec)]; exact hC3, e⟩
  have hbm4' : ∀ c C', (X3.setNode b l r').t.bs !! c = some C' → ∃ C, X.t.bs !! c = some C ∧
      C'.bm = C.bm := by
    intro c C' hC'
    rw [hX4] at hC'
    have hC'' : (X3.t.bs.insert b { B3 with ns := B3.ns.insert l r' }) !! c = some C' := hC'
    by_cases ec : c = b
    · subst ec; rw [GMap.lookup_insert] at hC''; cases hC''
      obtain ⟨C, hC, e⟩ := k8 c B3 hB3
      exact ⟨C, hC, e⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm ec)] at hC''
      exact k8 c C' hC''
  have hloc4 : ∀ n, bktLoc (X3.setNode b l r') n = bktLoc X n := by
    intro n
    unfold bktLoc
    rw [hrl4]
    cases hR : X.t.bs !! X.rl with
    | none =>
      cases hR' : (X3.setNode b l r').t.bs !! X.rl with
      | none => rfl
      | some R' =>
        obtain ⟨R, hR0, -⟩ := hbm4' _ R' hR'
        rw [hR] at hR0; cases hR0
    | some R =>
      obtain ⟨R', hR', e⟩ := hbm4 _ R hR
      rw [hR']; simp only [Option.bind_some]; rw [e]
  have hX4t : (X3.setNode b l r').t.t = X.t.t := by rw [hX4]; exact k4
  refine ⟨gensOK_congr T X _ hh4 hloc4 hgens, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, fun fl hfl => ?_⟩, hrl4⟩
  · exact liveReach_setNode X3 b l B3 rl r' hB3 hrl e6 e8 (liveReach_matGrow hmg hok hwr.1)
  · rw [hX4t]; exact hwr.2.1
  · intro C hC k c hk
    rw [hrl4] at hC ⊢
    obtain ⟨C0, hC0, e⟩ := hbm4' _ C hC
    exact hwr.2.2 C0 hC0 k c (by rw [← e]; exact hk)
  · rw [hX4]; exact k3
  · rw [hX4]; exact k5
  · have h3 := flViewU_matGrow X X3 fl b hok hmg hfl
    exact flViewU_setNode X3 fl b l B3 rl r' hB3 hrl hlf e5 e3 (by rw [k2]; exact hroot) h3


/-- `node.put(newKey, newKey, value, 0, 0)`'s entry (`Bucket.Put`): plain, no child page, its key
and value persistent heap bytes. -/
def putEnt (kb vb : List w8) : WEntry :=
  ⟨W32 0, W64 0, kb, vb, Src.own DFrac.discard, Src.own DFrac.discard⟩

theorem setNode_self' (X : WX) (bl l : Loc) (B : BRec) (r : NRec) (hB : X.t.bs !! bl = some B)
    (hr : B.ns !! l = some r) : X.setNode bl l r = X := by
  unfold WX.setNode WX.setBkt
  rw [hB]
  simp only
  rw [GMap.insert_id _ _ _ hr]
  rw [show ({ B with ns := B.ns } : BRec) = B from rfl, GMap.insert_id _ _ _ hB]

theorem withWs_self (X : WX) (bl l : Loc) (B : BRec) (r : NRec) (hB : X.t.bs !! bl = some B)
    (hr : B.ns !! l = some r) : X.withWs bl l r.ws = X := by
  unfold WX.withWs
  rw [hB]
  simp only [hr]
  rw [show ({ r with ws := r.ws } : NRec) = r from rfl, GMap.insert_id _ _ _ hr]
  rw [show ({ B with ns := B.ns } : BRec) = B from rfl, GMap.insert_id _ _ _ hB]

/-- The data facts `wtxData_put'`/`wtxData_del'` need of the handle's bucket after the
materializations: its name's location, injective, and its leaves plain. -/
theorem data_pre (T : TxView) (X X3 : WX) (n : GoString) (b l : Loc) (B3 : BRec) (rl : NRec)
    (hgens : gensOK T X) (hwr : wrFacts X) (hbl : bktLoc X n = some b) (hmg : matGrow X X3 b)
    (hok3 : wOK X3) (hB3 : X3.t.bs !! b = some B3) (hrl : B3.ns !! l = some rl)
    (hlf : rl.nv.isLeaf' = true) :
    bktLoc X3 n = some b ∧ (∀ n', bktLoc X3 n' = some b → n' = n) ∧
      (∀ w ∈ rl.ws, ¬ isBktFlag w.flags) ∧ nodeWs X3 b l = some rl.ws ∧ b ≠ X3.rl := by
  have hroot := bktLoc_ne_root X hwr n b hbl
  have k2 := (matGrow_keepW hmg).2.1
  have hroot3 : b ≠ X3.rl := by rw [k2]; exact hroot
  refine ⟨by rw [bktLoc_matGrow hmg]; exact hbl, fun n' h => ?_, fun w hw hf => ?_, ?_, hroot3⟩
  · rw [bktLoc_matGrow hmg] at h
    have h1 := hgens.2.1 n b hbl
    have h2 := hgens.2.1 n' b h
    rw [h1] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    exact h2.1.symm
  · exact hroot3 ((hok3.1.2.1.2.2.1 b B3 hB3 l rl hrl hlf w hw).1 hf)
  · unfold nodeWs; rw [hB3]; simp [hrl]

/-- **`Bucket.Put`'s post** (see the module doc). -/
theorem putPost (T : TxView) (X X3 : WX) (n : GoString) (b l : Loc) (B3 : BRec) (rl : NRec)
    (kb vb : List w8) (s : GoSlice) (ins : List Inode)
    (hok : wOK X) (hcur : T.cur = wtxData X) (hgens : gensOK T X) (hwr : wrFacts X)
    (hbl : bktLoc X n = some b) (hmg : matGrow X X3 b) (hok3 : wOK X3) (hd3 : objsDisj X3.t)
    (hB3 : X3.t.bs !! b = some B3) (hrl : B3.ns !! l = some rl) (hlf : leafFor X3 b kb l)
    (hk : 0 < kb.length) (hbnd : kb.length + vb.length ≤ bboltEntryMax)
    (hins : ins.length = (wsPutAt rl.ws kb (putEnt kb vb)).length) :
    wOK (X3.setNode b l (rl.withEnts s ins (wsPutAt rl.ws kb (putEnt kb vb)))) ∧
      wtxData (X3.setNode b l (rl.withEnts s ins (wsPutAt rl.ws kb (putEnt kb vb)))) =
        T.cur.insert n ((T.cur !! n).getD ∅ |>.insert kb vb) ∧
      gensOK T (X3.setNode b l (rl.withEnts s ins (wsPutAt rl.ws kb (putEnt kb vb)))) ∧
      wrFacts (X3.setNode b l (rl.withEnts s ins (wsPutAt rl.ws kb (putEnt kb vb)))) ∧
      XclKeep X (X3.setNode b l (rl.withEnts s ins (wsPutAt rl.ws kb (putEnt kb vb)))) := by
  have hlf0 : rl.nv.isLeaf' = true := by
    obtain ⟨B0, r0, bnd, hB0, hr0, hlf0, -⟩ := hlf
    rw [hB3] at hB0; cases hB0; rw [hrl] at hr0; cases hr0; exact hlf0
  have hroot := bktLoc_ne_root X hwr n b hbl
  obtain ⟨hbl3, hinj, hplain, hws, hroot3⟩ :=
    data_pre T X X3 n b l B3 rl hgens hwr hbl hmg hok3 hB3 hrl hlf0
  have hfl0 : ¬ isBktFlag (W32 0) := by unfold isBktFlag; decide
  obtain ⟨g1, g2, g3, -⟩ := post_common T X X3 b l B3 rl _ hok hgens hwr hmg hB3 hrl hlf0 hroot
    (sameShapeU_withEnts rl s ins _)
  refine ⟨wOK_putLeaf X3 b l B3 rl kb (putEnt kb vb) s ins hok3 hd3 hroot3 hlf hB3 hrl rfl hk hbnd
    hfl0 rfl (by simp [putEnt]) (by simp [putEnt]) hins, ?_, g1, g2, g3⟩
  have hpw : wsPw rl.ws :=
    wsSorted_pw _ ((wOK_bktClean X3 hok3 b B3 hB3).2.2.2.2.2.2.2.1 l rl hrl).2.2.2.1
  rw [wtxData_setNode X3 b l B3 rl (rl.withEnts s ins (wsPutAt rl.ws kb (putEnt kb vb))) hB3 hrl rfl]
  show wtxData (X3.withWs b l (wsPutAt rl.ws kb (putEnt kb vb))) = _
  rw [show wsPutAt rl.ws kb (putEnt kb vb) = wsPut rl.ws (putEnt kb vb) from
    wsPutAt_wsPut rl.ws (putEnt kb vb) hpw]
  rw [wtxData_put' X3 n b l rl.ws (putEnt kb vb) hok3 hbl3 hinj hlf hws hfl0
    (by intro h; have h' : kb = [] := h; subst h'; exact absurd hk (by simp)) (fun w hw _ => hplain w hw),
    wtxData_matGrow X X3 b hok hmg, ← hcur]
  rfl

/-- **`Bucket.Delete`'s post, the key found** (see the module doc). -/
theorem delPost (T : TxView) (X X3 : WX) (n : GoString) (b l : Loc) (B3 : BRec) (rl : NRec)
    (kb : List w8) (s : GoSlice) (ins : List Inode)
    (hok : wOK X) (hcur : T.cur = wtxData X) (hgens : gensOK T X) (hwr : wrFacts X)
    (hbl : bktLoc X n = some b) (hmg : matGrow X X3 b) (hok3 : wOK X3) (hd3 : objsDisj X3.t)
    (hB3 : X3.t.bs !! b = some B3) (hrl : B3.ns !! l = some rl) (hlf : leafFor X3 b kb l)
    (hins : ins.length = (wsDelAt rl.ws kb).length) :
    wOK (X3.setNode b l (rl.withEntsU s ins (wsDelAt rl.ws kb) true)) ∧
      wtxData (X3.setNode b l (rl.withEntsU s ins (wsDelAt rl.ws kb) true)) =
        T.cur.insert n ((T.cur !! n).getD ∅ |>.delete kb) ∧
      gensOK T (X3.setNode b l (rl.withEntsU s ins (wsDelAt rl.ws kb) true)) ∧
      wrFacts (X3.setNode b l (rl.withEntsU s ins (wsDelAt rl.ws kb) true)) ∧
      XclKeep X (X3.setNode b l (rl.withEntsU s ins (wsDelAt rl.ws kb) true)) := by
  have hlf0 : rl.nv.isLeaf' = true := by
    obtain ⟨B0, r0, bnd, hB0, hr0, hlf0, -⟩ := hlf
    rw [hB3] at hB0; cases hB0; rw [hrl] at hr0; cases hr0; exact hlf0
  have hroot := bktLoc_ne_root X hwr n b hbl
  obtain ⟨hbl3, hinj, hplain, hws, hroot3⟩ :=
    data_pre T X X3 n b l B3 rl hgens hwr hbl hmg hok3 hB3 hrl hlf0
  obtain ⟨g1, g2, g3, -⟩ := post_common T X X3 b l B3 rl _ hok hgens hwr hmg hB3 hrl hlf0 hroot
    (sameShapeU_withEntsU rl s ins _ true)
  refine ⟨wOK_delLeaf X3 b l B3 rl kb s ins hok3 hd3 hroot3 hB3 hrl hlf0 hins, ?_, g1, g2, g3⟩
  have hpw : wsPw rl.ws :=
    wsSorted_pw _ ((wOK_bktClean X3 hok3 b B3 hB3).2.2.2.2.2.2.2.1 l rl hrl).2.2.2.1
  rw [wtxData_setNode X3 b l B3 rl (rl.withEntsU s ins (wsDelAt rl.ws kb) true) hB3 hrl rfl]
  show wtxData (X3.withWs b l (wsDelAt rl.ws kb)) = _
  rw [wsDelAt_wsDel rl.ws kb hpw]
  rw [wtxData_del' X3 n b l rl.ws kb hok3 hbl3 hinj hlf hws (fun w hw _ => hplain w hw),
    wtxData_matGrow X X3 b hok hmg, ← hcur]

/-- **`Bucket.Delete`'s post, the key not found**: the records are the materializations', the
data unchanged (the key in no entry). -/
theorem delPostNF (T : TxView) (X X3 : WX) (n : GoString) (b l : Loc) (B3 : BRec) (rl : NRec)
    (kb : List w8)
    (hok : wOK X) (hcur : T.cur = wtxData X) (hgens : gensOK T X) (hwr : wrFacts X)
    (hbl : bktLoc X n = some b) (hmg : matGrow X X3 b) (hok3 : wOK X3)
    (hB3 : X3.t.bs !! b = some B3) (hrl : B3.ns !! l = some rl) (hlf : leafFor X3 b kb l)
    (hnf : ¬ wsFound rl.ws kb) :
    wtxData X3 = T.cur.insert n ((T.cur !! n).getD ∅ |>.delete kb) ∧
      gensOK T X3 ∧ wrFacts X3 ∧ XclKeep X X3 := by
  have hlf0 : rl.nv.isLeaf' = true := by
    obtain ⟨B0, r0, bnd, hB0, hr0, hlf0, -⟩ := hlf
    rw [hB3] at hB0; cases hB0; rw [hrl] at hr0; cases hr0; exact hlf0
  have hroot := bktLoc_ne_root X hwr n b hbl
  obtain ⟨hbl3, hinj, hplain, hws, hroot3⟩ :=
    data_pre T X X3 n b l B3 rl hgens hwr hbl hmg hok3 hB3 hrl hlf0
  obtain ⟨g1, g2, g3, -⟩ := post_common T X X3 b l B3 rl rl hok hgens hwr hmg hB3 hrl hlf0 hroot
    (by unfold sameShapeU; simp)
  rw [setNode_self' X3 b l B3 rl hB3 hrl] at g1 g2 g3
  refine ⟨?_, g1, g2, g3⟩
  have hpw : wsPw rl.ws :=
    wsSorted_pw _ ((wOK_bktClean X3 hok3 b B3 hB3).2.2.2.2.2.2.2.1 l rl hrl).2.2.2.1
  have hdel : wsDel rl.ws kb = rl.ws := by
    rw [← wsDelAt_wsDel rl.ws kb hpw]; unfold wsDelAt; rw [if_neg hnf]
  have := wtxData_del' X3 n b l rl.ws kb hok3 hbl3 hinj hlf hws (fun w hw _ => hplain w hw)
  rw [hdel, withWs_self X3 b l B3 rl hB3 hrl] at this
  rw [this, wtxData_matGrow X X3 b hok hmg, ← hcur]

end wokput

end Write

end bbolt
end EtcdGrove
end Perennial
