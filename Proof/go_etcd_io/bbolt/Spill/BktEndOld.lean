/-
`Bucket.spill`'s root loop's end (U9x10, `notes/bbolt-proof-plan.md`): **an old value of the root
bucket holds its writer's data** (for `endEls`, `BktEndRoot.end_els` and `BktEndNil.nil_els`).
A root entry the loop does not rewrite keeps its value `v0`: an unopened bucket's (`oldU`), or a
cached child's without a root node (`oldN`). Its tree is a `bvalS` over the view, holding plain
entries (`bvalData`): for an unopened bucket its base tree's (`bktEntries`), read from its leaf
node's `bvalOK` or from the view page's `matNest` (`Write.BoundNest`); for a cached child its
logical entries (`lbktEnts`), its view tree read by its walk (`WOpen.lleaves_viewL_fuel`) and plain
by `posShape` (a bucket other than the root). An inline cached child's page is its value's
(`cachedNil_ipg`: `bktNested`'s inline clause, maintainer 13's item 5).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktEndElsCore
public import Proof.go_etcd_io.bbolt.Spill.BktEndDisj
public import Proof.go_etcd_io.bbolt.Spill.BktEndVals
public import Proof.go_etcd_io.bbolt.Spill.BktEndRootLeaf
public import Proof.go_etcd_io.bbolt.Write.BoundNest
public import Proof.go_etcd_io.bbolt.Read.WOpenWOK

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section old
variable [GooseExts]

/-- A tree's own pages have keys. -/
theorem ownHas_treeKeys {P : Pages} {a p : Nat} (h : ownHas P a p) :
    ∀ {lo hi : Option (List w8)}, treeKeys P a lo hi → ∃ lo' hi', treeKeys P p lo' hi' := by
  induction h with
  | root a pg hpg => intro lo hi hk; exact ⟨lo, hi, hk⟩
  | child a pg i x hpg hf hix _ ih =>
    intro lo hi hk
    cases hk with
    | leaf _ pg' _ _ hpg' hfl _ _ =>
      rw [hpg] at hpg'; cases hpg'; rw [hf] at hfl
      exact absurd hfl (by unfold branchPageFlag leafPageFlag; decide)
    | branch _ pg' _ _ _ hpg' _ _ _ _ hch =>
      rw [hpg] at hpg'; cases hpg'; exact ih (hch i hix)

/-- `bvalData` of a value whose leaves (`bktLeafPg`) are plain, its own entries. -/
theorem bvalData_of_plain {P : Pages} {hwm : Nat} {v : List w8} {S : List Nat}
    (hS : bvalS P hwm v S)
    (hpl : ∀ bpg, bktLeafPg P v bpg → ∀ j < pageCount bpg,
      leafFlags bpg j % 2 = 0 ∧ 0 < leafKsize bpg j ∧
        leafKsize bpg j + leafVsize bpg j ≤ bboltEntryMax) :
    bvalData P v (bktEntries P v) := by
  refine ⟨fun h0 => ⟨?_, hpl _ (Or.inl ⟨h0, rfl⟩)⟩, fun h0 => ⟨?_, ?_⟩⟩
  · unfold bktEntries bktLeaves; rw [if_pos h0, List.flatMap_singleton]
  · unfold bktEntries bktLeaves; rw [if_neg h0]; rfl
  · intro bpg hbpg j hj
    rcases hS.2 with ⟨hr0, -⟩ | ⟨-, hh, hs⟩
    · exact absurd hr0 h0
    obtain ⟨id', -, -, ho, hp', hfl', -, -⟩ :=
      leavesF_page _ _ _ _ _ _ hs.wf hs.keys bpg hbpg
    exact hpl bpg (Or.inr ⟨h0, id', ho, hp', hfl'⟩) j hj

/-- **A bucket entry of a view leaf page**: its value a `bvalS` over the view, its leaves plain. -/
theorem oldPage {X : WX} {C : CommitSt} (hok : wOKR X) (hcok : treeOK C)
    (hcp : X.v.pages = C.pages) {p : Nat} {pg : List w8} (hpg : X.v.pages !! p = some pg)
    (hlf : pageFlags pg = leafPageFlag) {i : Nat} (hi : i < pageCount pg)
    (hbf : leafFlags pg i % 2 = bucketLeafFlag) :
    ∃ hwm S, bvalS X.v.pages hwm (leafValue pg i) S ∧
      bvalData X.v.pages (leafValue pg i) (bktEntries X.v.pages (leafValue pg i)) := by
  have hvw : viewWF X.v := hok.2.2.2.2.2.2.2
  have hpgC : C.pages !! p = some pg := by rw [← hcp]; exact hpg
  have hstr := hcok.1
  have hp : treeHas C.pages C.root p := by
    have e : treePages C.pages C.root !! p = some pg := by rw [hcok.2.1]; exact hpgC
    rw [treePages_lookup] at e
    split at e
    · assumption
    · cases e
  obtain ⟨pg0, hpg0⟩ := treeWF_page_some hstr.1
  have hown := ownHas_of_bktLeaf hcok (ownHas.root _ pg0 hpg0) hp ⟨pg, hpgC, hlf, i, hi, hbf⟩
  obtain ⟨lo, hi', hk⟩ := ownHas_treeKeys hown hstr.2.2.1
  have hwfp : treeWF C.pages C.hwm p := treeWF_ownHas hown hstr.1
  have hbw : bucketWF C.pages C.hwm (leafValue pg i) := bucketWF_of_leaf hwfp hpgC hlf hi hbf
  have hkb : inBucketRoot (leafValue pg i) ≠ 0 →
      treeKeys C.pages (inBucketRoot (leafValue pg i)) none none := by
    cases hk with
    | leaf _ pg3 _ _ hpg3 _ _ hkb => rw [hpgC] at hpg3; cases hpg3; exact hkb i hi hbf
    | branch _ pg3 _ _ _ hpg3 hf3 _ _ _ _ =>
      rw [hpgC] at hpg3; cases hpg3; rw [hlf] at hf3
      exact absurd hf3 (by unfold branchPageFlag leafPageFlag; decide)
  have hgood : inBucketRoot (leafValue pg i) = 0 → inlineGood (inlinePage (leafValue pg i)) :=
    (((mat_strict X.v hvw).1 p pg hpg).1 hlf i hi).2 hbf
  obtain ⟨S, hS, -⟩ := bvalS_of_wf (X := X) hcok hcp (Nat.le_refl C.hwm) (fun _ _ h => h)
    (by rw [hcp]; exact hbw) hgood (by rw [hcp]; exact hkb)
  exact ⟨C.hwm, S, hS, bvalData_of_plain hS (viewWF_matNest X.v hvw p pg hpg hlf i hi hbf)⟩

/-- **An uncached bucket entry of a leaf node of the root**: its value a `bvalS` over the view,
its leaves plain (`bvalOK`). -/
theorem oldNode {X : WX} {C : CommitSt} (hok : wOKR X) (hcok : treeOK C)
    (hcp : X.v.pages = C.pages) {R : BRec} (hR : X.t.bs !! X.rl = some R) {l : Loc} {r : NRec}
    (hr : R.ns !! l = some r) (hl : r.nv.isLeaf' = true) {w : WEntry} (hw : w ∈ r.ws)
    (hb : isBktFlag w.flags) (hnc : R.bm !! w.key = none) :
    ∃ hwm S, bvalS X.v.pages hwm w.value S ∧
      bvalData X.v.pages w.value (bktEntries X.v.pages w.value) := by
  have hcl := (hok.1.2.2.2.2.2 X.rl R hR).1
  have hnc' := (hcl.2.2.2.2.2.2.2.1 l r hr).2.2.2.2.2.2.2.2.2.2.2.1 hl w hw hb
  have hv := hnc'.1 (by rw [hnc]; rfl)
  obtain ⟨S, hS, -⟩ := bvalS_uncached hok hcok hcp (Nat.le_refl C.hwm) (fun _ _ h => h) hR hr hl
    hw hb hnc
  refine ⟨C.hwm, S, hS, bvalData_of_plain hS fun bpg hbpg j hj => ?_⟩
  have hb2 := hbpg
  rcases hb2 with ⟨h0, rfl⟩ | ⟨h0, -⟩
  · obtain ⟨hg, hbnd⟩ := hv.2.1 h0
    exact ⟨(hg.2.2.2.2 j hj).2, (hg.2.2.2.2 j hj).1, hbnd j hj⟩
  · exact hv.2.2 h0 bpg hbpg j hj

/-- **An unopened bucket's value** (see the module doc). -/
theorem oldU {X : WX} {C : CommitSt} (hok : wOKR X) (hcok : treeOK C)
    (hcp : X.v.pages = C.pages) {B : BRec} (hB : X.t.bs !! X.rl = some B)
    (h0 : B.ib.root' ≠ W64 0) {n v0 : List w8} (hm : (n, v0) ∈ rootEnts X)
    (hnc : B.bm !! n = none) :
    ∃ hwm S, bvalS X.v.pages hwm v0 S ∧ bvalData X.v.pages v0 (bktEntries X.v.pages v0) := by
  have hcl : bktClean X.v X.t.mv.pgid'.toNat X.rl B := (hok.1.2.2.2.2.2 X.rl B hB).1
  obtain ⟨we, -, hbk, hwk, hwv, hsrc⟩ := rootEnt_src hB hcl h0 hm
  subst hwv
  rcases hsrc with ⟨l, r, hr, hl, hw⟩ | ⟨c, p, pg, i, -, -, hpg, hlf, hi, rfl⟩
  · exact oldNode hok hcok hcp hB hr hl hw hbk (by rw [hwk]; exact hnc)
  · have e : (pageW pg i).value = leafValue pg i := (mat_pageW_leaf pg i hlf).2.2.2
    rw [e]
    exact oldPage hok hcok hcp hpg hlf hi (pageW_bkt hlf hbk)

/-- **An inline cached child without a root node reads its value's page** (its `ipg`):
`bktNested`'s inline clause (maintainer 13, item 5) at the child's entry, whose value is the
root entry's `v` (`allEnts_key_injR`). -/
theorem cachedNil_ipg {X : WX} (hok : wOKR X) (hreach : liveReach X) {B : BRec}
    (hB : X.t.bs !! X.rl = some B) (h0 : B.ib.root' ≠ W64 0) (hrt : rtOK X X.rl)
    (h64 : ∀ p pg, X.v.pages !! p = some pg → p < 2 ^ 64)
    {k : GoString} {c : Loc} (hk : B.bm !! k = some c) {Cc : BRec} (hc : X.t.bs !! c = some Cc)
    (hrn : Cc.bv.rootNode' = null) {v : List w8} (hm : (k, v) ∈ rootEnts X)
    (hib : Cc.ib = ibOf v) (hz : inBucketRoot v = 0) : Cc.ipg = inlinePage v := by
  obtain ⟨Cc', v', hCc', hent, -, -, -, -, hipg⟩ := (hok.2.1 X.rl B hB).2 k c hk
  rw [hc] at hCc'; cases hCc'
  have hcl : bktClean X.v X.t.mv.pgid'.toNat X.rl B := (hok.1.2.2.2.2.2 X.rl B hB).1
  obtain ⟨we', hwe', hk', hv', -⟩ := entryIn_rootEnts hok hreach hB h0 hrt h64 hent
  obtain ⟨we, hwe, -, hwk, hwv, -⟩ := rootEnt_src hB hcl h0 hm
  have := allEnts_key_injR X hok X.rl B hB we we' hwe hwe' (hwk.trans hk'.symm)
  have hvv : v' = v := by rw [← hv', ← this, hwv]
  subst hvv
  have hr : Cc.ib.root'.toNat = inBucketRoot v' := by rw [hib]; rfl
  exact hipg (BitVec.eq_of_toNat_eq (by rw [hr, hz]; rfl)) hrn

/-- The leaves of a bucket without nodes and with a root page: its view tree's. -/
theorem nilBkt_leavesR {X : WX} {c : Loc} {Cc : BRec} (hok : wOKR X)
    (hc : X.t.bs !! c = some Cc) (hrn : Cc.bv.rootNode' = null) (hC0 : Cc.ib.root' ≠ W64 0) :
    X.leaves c = (treeLeaves X.v.pages Cc.ib.root'.toNat).map pageWs := by
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  have hcl := (hok.1.2.2.2.2.2 c Cc hc).1
  have hnm : Cc.nm = ∅ := (hcl.2.2.1 hrn).2
  have hrp : X.rootPid c = Cc.ib.root' := by unfold WX.rootPid; rw [hc]; rfl
  have hres : ∀ p, resolve Cc p = none := by
    intro p; unfold resolve; split
    · simp [hrn]
    · rw [hnm]; rfl
  unfold WX.leaves
  rw [hrp]
  have hL : ∀ q, ltree X c q = WOpen.viewL X.v c c q := by
    intro q
    unfold ltree WOpen.viewL; rw [hc]; simp only [hres, ↓reduceIte]
    unfold wpageAt; rw [if_neg hC0]
    cases X.v.pages !! q.toNat <;> rfl
  rw [WOpen.lleaves_congr' _ (WOpen.viewL X.v c) c hL]
  have hf : X.fuel = X.v.pages.size + 1 + X.t.bs.size := by unfold WX.fuel; omega
  rw [hf, WOpen.lleaves_viewL_fuel X.v hv c _ _]

/-- The leaves of a bucket without nodes: its value's (see the module doc). -/
theorem nilBkt_leaves {X : WX} {c : Loc} {Cc : BRec} (hok : wOKR X) (hc : X.t.bs !! c = some Cc)
    (hrn : Cc.bv.rootNode' = null) {v : List w8} (hib : Cc.ib = ibOf v)
    (hipg : inBucketRoot v = 0 → Cc.ipg = inlinePage v) :
    X.leaves c = (bktLeaves X.v.pages v).map pageWs := by
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  have hcl := (hok.1.2.2.2.2.2 c Cc hc).1
  have hnm : Cc.nm = ∅ := (hcl.2.2.1 hrn).2
  have hrp : X.rootPid c = Cc.ib.root' := by unfold WX.rootPid; rw [hc]; rfl
  have hres : ∀ p, resolve Cc p = none := by
    intro p; unfold resolve; split
    · simp [hrn]
    · rw [hnm]; rfl
  have hr : Cc.ib.root'.toNat = inBucketRoot v := by rw [hib]; rfl
  unfold WX.leaves bktLeaves
  rw [hrp]
  by_cases h0 : inBucketRoot v = 0
  · rw [if_pos h0]
    have hC0 : Cc.ib.root' = W64 0 := by
      apply BitVec.eq_of_toNat_eq; rw [hr, h0]; rfl
    have hL : ltree X c (W64 0) = some (true, pageWs (inlinePage v)) := by
      unfold ltree; rw [hc]; simp only [hres]
      unfold wpageAt; rw [if_pos hC0, if_pos rfl, hipg h0]
      have hg := (hcl.1 hC0 hrn).2.2.1
      rw [hipg h0] at hg
      simp only [Option.map_some, hg.2.1, decide_true]
    rw [hC0]
    obtain ⟨n, hn⟩ : ∃ n, X.fuel = n + 1 := ⟨_, rfl⟩
    rw [hn]
    simp only [lleaves]
    rw [hL]
    rfl
  · rw [if_neg h0]
    have hC0 : Cc.ib.root' ≠ W64 0 := by
      intro e; apply h0; rw [← hr, e]; rfl
    have e := nilBkt_leavesR hok hc hrn hC0
    unfold WX.leaves at e; rw [hrp] at e; rw [e, hr]

/-- **A cached child's value, the child without a root node** (see the module doc). -/
theorem oldN {X : WX} {C : CommitSt} (hok : wOKR X) (hreach : liveReach X) (hcok : treeOK C)
    (hcp : X.v.pages = C.pages) {B : BRec} (hB : X.t.bs !! X.rl = some B)
    (h0 : B.ib.root' ≠ W64 0) (hrt : rtOK X X.rl)
    (h64 : ∀ p pg, X.v.pages !! p = some pg → p < 2 ^ 64) {n v0 : List w8}
    (hm : (n, v0) ∈ rootEnts X) {c : Loc} (hk : B.bm !! n = some c) {Cc : BRec}
    (hc : X.t.bs !! c = some Cc) (hrn : Cc.bv.rootNode' = null) (hcrl : c ≠ X.rl) :
    ∃ hwm S, bvalS X.v.pages hwm v0 S ∧ bvalData X.v.pages v0 (lbktEnts X c) := by
  obtain ⟨hib, S, hS, -⟩ := nil_val hok hreach hcok hcp (Nat.le_refl C.hwm) (fun _ _ h => h) hB h0
    hrt h64 hk hc hrn hm
  have hcl := (hok.1.2.2.2.2.2 c Cc hc).1
  have hr : Cc.ib.root'.toNat = inBucketRoot v0 := by rw [hib]; rfl
  have hipg := cachedNil_ipg hok hreach hB h0 hrt h64 hk hc hrn hm hib
  -- the child's leaves are plain
  have hpl : ∀ bpg, bktLeafPg X.v.pages v0 bpg → ∀ j < pageCount bpg,
      leafFlags bpg j % 2 = 0 ∧ 0 < leafKsize bpg j ∧
        leafKsize bpg j + leafVsize bpg j ≤ bboltEntryMax := by
    intro bpg hbpg j hj
    rcases hbpg with ⟨hz, rfl⟩ | ⟨hz, id, ho, hp, hfl⟩
    · have hC0 : Cc.ib.root' = W64 0 := by
        apply BitVec.eq_of_toNat_eq; rw [hr, hz]; rfl
      have hg := (hcl.1 hC0 hrn).2.2
      rw [hipg hz] at hg
      exact ⟨(hg.1.2.2.2.2 j hj).2, (hg.1.2.2.2.2 j hj).1, hg.2 j hj⟩
    · have hC0 : Cc.ib.root' ≠ W64 0 := by
        intro e; apply hz; rw [← hr, e]; rfl
      have hpos : posRoot Cc (inBucketRoot v0) := Or.inl ⟨hrn, hC0, hr.symm⟩
      have hs := hok.1.2.1.2.2.2.1 c Cc hc _ id bpg hpos ho hp hfl j hj
      have hne : ¬ (leafFlags bpg j % 2 = bucketLeafFlag) := fun h => hcrl (hs.1.1 h)
      unfold bucketLeafFlag at hne
      exact ⟨by omega, hs.2.1.1, hs.2.1.2⟩
  have hd := bvalData_of_plain hS hpl
  refine ⟨C.hwm, S, hS, ?_⟩
  have e : lbktEnts X c = bktEntries X.v.pages v0 := by
    unfold lbktEnts bktEntries
    rw [nilBkt_leaves hok hc hrn hib hipg, List.flatMap_map]
    apply Write.flatMap_congr'
    intro pg hpg
    have hpl' : bktLeafPg X.v.pages v0 pg ∧ pageFlags pg = leafPageFlag := by
      unfold bktLeaves at hpg
      split at hpg
      · rename_i hz
        simp only [List.mem_singleton] at hpg; subst hpg
        have hC0 : Cc.ib.root' = W64 0 := by
          apply BitVec.eq_of_toNat_eq; rw [hr, hz]; rfl
        have hg := (hcl.1 hC0 hrn).2.2.1
        rw [hipg hz] at hg
        exact ⟨Or.inl ⟨hz, rfl⟩, hg.2.1⟩
      · rename_i hz
        rcases hS.2 with ⟨hr0, -⟩ | ⟨-, hh, hs⟩
        · exact absurd hr0 hz
        obtain ⟨id', -, -, ho, hp', hfl', -, -⟩ :=
          leavesF_page _ _ _ _ _ _ hs.wf hs.keys pg hpg
        exact ⟨Or.inr ⟨hz, id', ho, hp', hfl'⟩, hfl'⟩
    exact WOpen.plain_pageWs pg hpl'.2 fun j hj => (hpl pg hpl'.1 j hj).1
  rw [e]; exact hd

/-- **The writer's data of a root entry's name** (the root's names distinct). -/
theorem bktData_mem {X : WX} (hok : wOKR X) {B : BRec} (hB : X.t.bs !! X.rl = some B)
    (h0 : B.ib.root' ≠ W64 0) {n v0 : List w8} (hm : (n, v0) ∈ rootEnts X) :
    bktData X n = some (bktDataOf X n v0) := by
  have hcl : bktClean X.v X.t.mv.pgid'.toNat X.rl B := (hok.1.2.2.2.2.2 X.rl B hB).1
  unfold bktData
  cases hf : (rootEnts X).find? (fun e => decide (e.1 = n)) with
  | none =>
    have := List.find?_eq_none.1 hf (n, v0) hm
    simp at this
  | some e =>
    have hem := List.mem_of_find?_eq_some hf
    have hen : e.1 = n := by simpa using List.find?_some hf
    obtain ⟨we, hwe, -, hwk, hwv, -⟩ := rootEnt_src hB hcl h0 hm
    obtain ⟨we', hwe', -, hwk', hwv', -⟩ := rootEnt_src hB hcl h0 (show (e.1, e.2) ∈ rootEnts X from hem)
    have := allEnts_key_injR X hok X.rl B hB we we' hwe hwe' (by rw [hwk, hwk', hen])
    subst this
    simp only [Option.map_some, hen]
    rw [← hwv', hwv]

end old

end Spill

end bbolt
end EtcdGrove
end Perennial
