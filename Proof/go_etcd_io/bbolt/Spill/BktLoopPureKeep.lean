/-
`Bucket.spill`'s root loop (U9x, `notes/bbolt-proof-plan.md`): **a bucket kept modulo sources**
(`bktKept`: its record `bktSim`, its nodes `nodeSim`), what a child's spill (`spFrame` for the other
buckets, then `setBkt` of the child) does to the root bucket and to the other children. Such a
bucket keeps its logical tree by data (`ltree_kept`), so its leaves, entries and finite tree
(`rtOK_kept`); its live nodes stay live when the new records' `derefPre` holds and the bucket is
still live (`live_kept`: a live node descends from its root node's root, and `derefPre` makes the
descendants of a live node live); and it stays searchable (`bktLocalOK_kept`) given the new
records' `liveFresh`, the view (but its base) and a mark not lower.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopInv
public import Proof.go_etcd_io.bbolt.Spill.STreeMono
public import Proof.go_etcd_io.bbolt.Spill.DerefRel
public import Proof.go_etcd_io.bbolt.Spill.UTreeFrame
public import Proof.go_etcd_io.bbolt.Write.Mat
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSMatT

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section keep
variable [GooseExts]

/-- **Bucket `bl` kept modulo sources** from `X` to `X'`: its record but its nodes, and its nodes
modulo sources. -/
def bktKept (X X' : WX) (bl : Loc) : Prop :=
  ∀ B, X.t.bs !! bl = some B → ∃ B', X'.t.bs !! bl = some B' ∧ bktSim B B' ∧
    ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l)

/-! ## The logical tree by data -/

theorem resolve_sim {B B' : BRec} (h : bktSim B B') (pid : w64) : resolve B' pid = resolve B pid := by
  unfold resolve; rw [h.1, h.2.1, h.2.2.1]

theorem ltree_kept {X X' : WX} {bl : Loc} {B B' : BRec} (hB : X.t.bs !! bl = some B)
    (hB' : X'.t.bs !! bl = some B') (hs : bktSim B B') (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l))
    (hv : X'.v.pages = X.v.pages) (pid : w64) :
    Write.ldat (ltree X' bl pid) = Write.ldat (ltree X bl pid) := by
  unfold ltree
  rw [hB, hB']
  simp only
  rw [resolve_sim hs]
  cases hr : resolve B pid with
  | some l =>
    simp only
    have h := hns l
    cases h1 : B.ns !! l with
    | none => rw [h1] at h; rw [optRel_none_l h]
    | some r =>
      rw [h1] at h
      obtain ⟨r', h2, hsim⟩ := optRel_some_l h
      rw [h2]
      simp only [Write.ldat, Option.map_some, Option.some.injEq, Prod.mk.injEq]
      exact ⟨nodeSim_isLeaf hsim, hsim.2.2.1⟩
  | none =>
    simp only
    unfold wpageAt
    rw [hs.2.1, hs.1, hs.2.2.2.2, hv]
    by_cases h0 : B.ib.root' = W64 0
    · simp only [h0, ↓reduceIte]
      try (by_cases hp : pid = W64 0 <;> simp [hp, Write.ldat])
    · simp only [h0, ↓reduceIte]
      try (cases X.v.pages !! pid.toNat <;> simp [Write.ldat])

theorem rootPid_kept {X X' : WX} {bl : Loc} {B B' : BRec} (hB : X.t.bs !! bl = some B)
    (hB' : X'.t.bs !! bl = some B') (hs : bktSim B B') : X'.rootPid bl = X.rootPid bl := by
  unfold WX.rootPid; rw [hB, hB']; simp [hs.2.1]

theorem leaves_kept {X X' : WX} {bl : Loc} {B B' : BRec} (hB : X.t.bs !! bl = some B)
    (hB' : X'.t.bs !! bl = some B') (hs : bktSim B B') (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l))
    (hv : X'.v.pages = X.v.pages) (hf : X'.fuel = X.fuel) :
    (X'.leaves bl).map (List.map wDat) = (X.leaves bl).map (List.map wDat) := by
  unfold WX.leaves
  rw [hf, rootPid_kept hB hB' hs]
  exact Write.lleaves_dat _ _ bl (ltree_kept hB hB' hs hns hv) _ _

theorem rtOK_kept {X X' : WX} {bl : Loc} {B B' : BRec} (hB : X.t.bs !! bl = some B)
    (hB' : X'.t.bs !! bl = some B') (hs : bktSim B B') (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l))
    (hv : X'.v.pages = X.v.pages) (hf : X'.fuel = X.fuel) (h : rtOK X bl) : rtOK X' bl := by
  obtain ⟨t, ht, hp, hh, D, hD⟩ := h
  obtain ⟨t', ht', hp', hh', hd'⟩ :=
    ltIs_ldat (ltree X) (ltree X') bl (ltree_kept hB hB' hs hns hv) t ht
  refine ⟨t', ht', by rw [hp', hp, rootPid_kept hB hB' hs], by rw [hh', hf]; exact hh, D, ?_⟩
  intro x hx; rw [hd'] at hx; exact hD x hx

/-- The fuel is kept when every bucket stays one. -/
theorem fuel_kept {X X' : WX} (hv : X'.v.pages = X.v.pages)
    (hbs : ∀ bl, (X'.t.bs !! bl).isSome = (X.t.bs !! bl).isSome) : X'.fuel = X.fuel :=
  fuel_eq X X' hv hbs

/-! ## Liveness -/

theorem nodeRootIn_kept {B B' : BRec} (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l))
    {a rt : Loc} (h : nodeRootIn B a rt) : nodeRootIn B' a rt := by
  induction h with
  | top n r hr hp =>
    have h := hns n; rw [hr] at h
    obtain ⟨r', hr', hs⟩ := optRel_some_l h
    exact nodeRootIn.top n r' hr' (by rw [nodeSim_parent hs]; exact hp)
  | up n rt r hr hp _ ih =>
    have h := hns n; rw [hr] at h
    obtain ⟨r', hr', hs⟩ := optRel_some_l h
    refine nodeRootIn.up n rt r' hr' (by rw [nodeSim_parent hs]; exact hp) ?_
    rw [nodeSim_parent hs]; exact ih

theorem descIn_kept {B B' : BRec} (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l))
    {a d : Loc} (h : descIn B a d) : descIn B' a d := by
  induction h with
  | self n => exact descIn.self n
  | child n c d r hr hc _ ih =>
    have h := hns n; rw [hr] at h
    obtain ⟨r', hr', hs⟩ := optRel_some_l h
    exact descIn.child n c d r' hr' (by rw [hs.2.2.2.2.1]; exact hc) ih

/-- The descendants of a live node are live (`derefPre`). -/
theorem live_desc {X : WX} (hp : derefPre X) {bl : Loc} {B : BRec} (hB : X.t.bs !! bl = some B)
    {a d : Loc} (h : descIn B a d) (ha : a ∈ X.live) : d ∈ X.live := by
  induction h with
  | self n => exact ha
  | child n c d r hr hc _ ih => exact ih ((hp.1 bl B n r hB hr ha).2.2.2 c hc).1

/-- **A live node of a kept, still live bucket stays live** (see the module doc). -/
theorem live_kept {X X' : WX} {bl : Loc} {B B' : BRec} (hB : X.t.bs !! bl = some B)
    (hB' : X'.t.bs !! bl = some B') (hs : bktSim B B')
    (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l)) (hreach : liveReach X)
    (hp' : derefPre X') (hbl : bl ∈ X'.liveB) {l : Loc} {r : NRec} (hr : B.ns !! l = some r)
    (hl : l ∈ X.live) : l ∈ X'.live := by
  obtain ⟨rt, hrt, hd⟩ := hreach.2 bl B l r hB hr hl
  have hrt' := nodeRootIn_kept hns hrt
  rw [← hs.1] at hrt'
  have hnn : B'.bv.rootNode' ≠ null := by
    intro e
    have := nodeRootIn_ns hrt'
    rw [e, (hp'.2.2.1 bl B' hB').2] at this
    cases this
  obtain ⟨rt', hrt'', hlive⟩ := (hp'.2.1 bl B' hB' hbl).2 hnn
  have e := nodeRootIn_unique hrt' hrt''
  subst e
  exact live_desc hp' hB' (descIn_kept hns hd) hlive

/-! ## Searchable -/

/-- A well-formed nested bucket's value is well-formed below a higher mark. -/
theorem bucketWF_hwm {P : Pages} {hwm hwm' : Nat} {v : List w8} (hle : hwm ≤ hwm')
    (h : bucketWF P hwm v) : bucketWF P hwm' v :=
  bucketWF.rec (pages := P) (hwm := hwm)
    (motive_1 := fun root _ => treeWF P hwm' root)
    (motive_2 := fun pg len _ => pageTreeWF P hwm' pg len)
    (motive_3 := fun v _ => bucketWF P hwm' v)
    (fun root pg h2 hlt hpg hid hlen _ ih => treeWF.page root pg h2 (by omega) hpg hid hlen ih)
    (fun pg len hfl hlw _ ih => pageTreeWF.leaf pg len hfl hlw ih)
    (fun pg len hfl hbw _ ih => pageTreeWF.branch pg len hfl
      ⟨hbw.1, hbw.2.1, hbw.2.2.1, fun i hi => ⟨(hbw.2.2.2.1 i hi).1, (hbw.2.2.2.1 i hi).2.1,
        by have := (hbw.2.2.2.1 i hi).2.2; omega⟩, hbw.2.2.2.2⟩ ih)
    (fun v h16 hr _ ih => bucketWF.file v h16 hr ih)
    (fun v h16 hr hfl _ ih => bucketWF.inline v h16 hr hfl ih)
    h

theorem bvalOK_hwm {P : Pages} {hwm hwm' : Nat} {v : List w8} (hle : hwm ≤ hwm')
    (h : bvalOK P hwm v) : bvalOK P hwm' v :=
  ⟨bucketWF_hwm hle h.1, h.2⟩

theorem pagePosAt_kept {B B' : BRec} (hs : bktSim B B')
    (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l)) (l : Loc) (i : Nat) (c : w64) :
    pagePosAt B' l i c ↔ pagePosAt B l i c := by
  constructor
  · rintro ⟨r', w', hr', hbr, hw', hc, hn⟩
    have h := hns l; rw [hr'] at h
    obtain ⟨r, hr, e⟩ := optRel_some_r h
    obtain ⟨w, hw, he⟩ := get_of_dat e.2.2.1 hw'
    exact ⟨r, w, hr, by rw [← nodeSim_isLeaf e]; exact hbr, hw, by rw [← wDat_pgid he]; exact hc,
      by rw [← hs.2.2.1]; exact hn⟩
  · rintro ⟨r, w, hr, hbr, hw, hc, hn⟩
    have h := hns l; rw [hr] at h
    obtain ⟨r', hr', e⟩ := optRel_some_l h
    have e' : r.ws.map wDat = r'.ws.map wDat := e.2.2.1.symm
    obtain ⟨w', hw', he⟩ := get_of_dat e' hw
    exact ⟨r', w', hr', by rw [nodeSim_isLeaf e]; exact hbr, hw', by rw [← wDat_pgid he]; exact hc,
      by rw [hs.2.2.1]; exact hn⟩

end keep

end Spill

end bbolt
end EtcdGrove
end Perennial
