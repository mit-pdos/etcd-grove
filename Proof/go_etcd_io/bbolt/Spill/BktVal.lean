/-
`Bucket.spill` (U9p, `notes/bbolt-proof-plan.md`): **the root's nested bucket values at the
spill** (`InitB.sb` for the root bucket's leaves, after the loop over the cached children). A value
the view's committed tree holds (`bvalOK` over the view, its keys bounded: `treeOK` gives the rest)
is a `bvalS` over any page map agreeing with the view, its slots the value's `bucketCovers`:

- an uncached nested bucket's entry in a root leaf node (`nodeClean`'s `bvalOK`, `nodeKeys`'
  last clause): `bvalS_uncached`;
- a cached child without a root node, whose entry the loop leaves: its value is the one
  `bktNested` names (`entryIn`), its header the child's (`C.ib = ibOf v`), its tree the child's
  (`bktClean`: well-formed; `bktKeysB`: keys): `bvalS_cachedNil`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTree
public import Proof.go_etcd_io.bbolt.Spill.STreeBase
public import Proof.go_etcd_io.bbolt.Spill.STreeAgree

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section val
variable [GooseExts]

/-- `bvalS_view` from the value's well-formedness and its inline page good. -/
theorem bvalS_of_wf {X : WX} {C : CommitSt} (hcok : treeOK C) (hcp : X.v.pages = C.pages)
    {hwm hwm' : Nat} (hch : C.hwm ≤ hwm) {P : Pages}
    (hag : ∀ x pg, X.v.pages !! x = some pg → P !! x = some pg) {v : List w8}
    (hwf : bucketWF X.v.pages hwm' v) (hgood : inBucketRoot v = 0 → inlineGood (inlinePage v))
    (hk : inBucketRoot v ≠ 0 → treeKeys X.v.pages (inBucketRoot v) none none) :
    ∃ S, bvalS P hwm v S ∧ ∀ s, s ∈ pgSlots P S ↔ bucketCovers X.v.pages v s := by
  cases hwf with
  | inline _ hlen h0 _ _ =>
    have hg := hgood h0
    refine ⟨[], ⟨hlen, Or.inl ⟨h0, rfl, hg⟩⟩, fun s => ?_⟩
    simp only [pgSlots, List.flatMap_nil, List.not_mem_nil, false_iff]
    rintro ⟨id, pg, hb, -⟩
    exact inlineGood_noHas hg h0 id hb
  | file _ hlen h0 hwf =>
    obtain ⟨pg, hpg⟩ := treeWF_page_some hwf
    rw [hcp] at hpg
    have ht : treeHas C.pages C.root (inBucketRoot v) := by
      have e : treePages C.pages C.root !! inBucketRoot v = some pg := by rw [hcok.2.1]; exact hpg
      rw [treePages_lookup] at e
      split at e
      · assumption
      · cases e
    obtain ⟨pht, hpht⟩ := hcok.1.2.2.2
    have hk' := hk h0
    rw [hcp] at hk'
    have hs := sTree_base C hcok ht hk' pht hpht
    have hagS : ∀ x ∈ subPages C.pages (inBucketRoot v), P !! x = C.pages !! x := by
      intro x hx
      obtain ⟨pgx, hpx⟩ := treeHas_page (mem_subPages.1 hx)
      rw [hpx]; exact hag x pgx (by rw [hcp]; exact hpx)
    refine ⟨subPages C.pages (inBucketRoot v), ⟨hlen, Or.inr ⟨h0, _, sTree_agree hagS hch hs⟩⟩,
      fun s => ?_⟩
    unfold pgSlots bucketCovers
    simp only [List.mem_flatMap]
    constructor
    · rintro ⟨x, hx, hsx⟩
      have htx := mem_subPages.1 hx
      obtain ⟨pgx, hpx⟩ := treeHas_page htx
      rw [hagS x hx, hpx] at hsx
      simp only [List.mem_range'] at hsx
      obtain ⟨i, hi, rfl⟩ := hsx
      exact ⟨x, pgx, bucketHas.file v x h0 (by rw [hcp]; exact htx), by rw [hcp]; exact hpx,
        by omega, by omega⟩
    · rintro ⟨id, pgi, hb, hpi, h1, h2⟩
      have htx : treeHas C.pages (inBucketRoot v) id := by
        cases hb with
        | file _ _ _ h => rw [← hcp]; exact h
        | inline _ _ h0' _ => exact absurd h0' h0
      have hx := mem_subPages.2 htx
      refine ⟨id, hx, ?_⟩
      rw [hagS id hx, ← hcp, hpi]
      simp only [List.mem_range']
      exact ⟨s - id, by omega, by omega⟩

/-- **A view value of the committed tree is a `bvalS`** over a page map `P` agreeing with the
view, at a mark above the committed one; its slots are its `bucketCovers`. -/
theorem bvalS_view {X : WX} {C : CommitSt} (hcok : treeOK C) (hcp : X.v.pages = C.pages)
    {hwm hwm' : Nat} (hch : C.hwm ≤ hwm) {P : Pages}
    (hag : ∀ x pg, X.v.pages !! x = some pg → P !! x = some pg) {v : List w8}
    (hv : bvalOK X.v.pages hwm' v)
    (hk : inBucketRoot v ≠ 0 → treeKeys X.v.pages (inBucketRoot v) none none) :
    ∃ S, bvalS P hwm v S ∧ ∀ s, s ∈ pgSlots P S ↔ bucketCovers X.v.pages v s :=
  bvalS_of_wf hcok hcp hch hag hv.1 (fun h0 => (hv.2.1 h0).1) hk

/-- **An uncached nested bucket's value in a leaf node of the root** is a `bvalS`. -/
theorem bvalS_uncached {X : WX} {C : CommitSt} (hok : wOKR X) (hcok : treeOK C)
    (hcp : X.v.pages = C.pages) {hwm : Nat} (hch : C.hwm ≤ hwm) {P : Pages}
    (hag : ∀ x pg, X.v.pages !! x = some pg → P !! x = some pg)
    {R : BRec} (hR : X.t.bs !! X.rl = some R) {l : Loc} {r : NRec} (hr : R.ns !! l = some r)
    (hl : r.nv.isLeaf' = true) {w : WEntry} (hw : w ∈ r.ws) (hb : isBktFlag w.flags)
    (hnc : R.bm !! w.key = none) :
    ∃ S, bvalS P hwm w.value S ∧ ∀ s, s ∈ pgSlots P S ↔ bucketCovers X.v.pages w.value s := by
  have hcl := (hok.1.2.2.2.2.2 X.rl R hR).1
  have hnc' := (hcl.2.2.2.2.2.2.2.1 l r hr).2.2.2.2.2.2.2.2.2.2.2.1 hl w hw hb
  have hv := hnc'.1 (by rw [hnc]; rfl)
  obtain ⟨bnd, hbk⟩ := (hok.2.1 X.rl R hR).1
  have hnk := hbk.2.2 l r hr
  exact bvalS_view hcok hcp hch hag hv
    (fun h0 => hnk.2.2.2.2.2 hl w hw hb h0 (by unfold opened; rw [hnc]; simp))

/-- **A cached child without a root node**: its value (`bktNested`'s) is a `bvalS`, its header
the child's. -/
theorem bvalS_cachedNil {X : WX} {C : CommitSt} (hok : wOKR X) (hcok : treeOK C)
    (hcp : X.v.pages = C.pages) {hwm : Nat} (hch : C.hwm ≤ hwm) {P : Pages}
    (hag : ∀ x pg, X.v.pages !! x = some pg → P !! x = some pg)
    {bl : Loc} {B : BRec} (hB : X.t.bs !! bl = some B) {k : GoString} {c : Loc}
    (hk : B.bm !! k = some c) {Cc : BRec} (hc : X.t.bs !! c = some Cc)
    (hrn : Cc.bv.rootNode' = null) :
    ∃ v S, entryIn X.v B k v ∧ Cc.ib = ibOf v ∧ bvalS P hwm v S ∧
      ∀ s, s ∈ pgSlots P S ↔ bucketCovers X.v.pages v s := by
  obtain ⟨Cc', v, hCc', hent, hlen, hinl, hroot, hib⟩ := (hok.2.1 bl B hB).2 k c hk
  rw [hc] at hCc'; cases hCc'
  have hibv := hib hrn
  have hcl := (hok.1.2.2.2.2.2 c Cc hc).1
  obtain ⟨bnd, hbk⟩ := (hok.2.1 c Cc hc).1
  have hr : Cc.ib.root'.toNat = inBucketRoot v := by rw [hibv]; rfl
  have hr0 : inBucketRoot v ≠ 0 → Cc.ib.root' ≠ W64 0 := by
    intro h e; rw [e] at hr; exact h hr.symm
  refine ⟨v, ?_⟩
  have hwf : bucketWF X.v.pages X.t.mv.pgid'.toNat v := by
    by_cases h0 : inBucketRoot v = 0
    · have hg := hinl h0
      refine bucketWF.inline v hlen h0 hg.2.1 (pageTreeWF.leaf _ _ hg.2.1 hg.2.2.1 fun i hi hbf => ?_)
      have := (hg.2.2.2.2 i hi).2
      rw [this] at hbf; simp [bucketLeafFlag] at hbf
    · have := (hcl.2.1 (hr0 h0)).2 hrn
      rw [hr] at this
      exact bucketWF.file v hlen h0 this
  obtain ⟨S, hS, hsl⟩ := bvalS_of_wf hcok hcp hch hag hwf hinl
    (fun h0 => by have := hbk.1 hrn (hr0 h0); rw [hr] at this; exact this)
  exact ⟨S, hent, hibv, hS, hsl⟩

end val

end Spill

end bbolt
end EtcdGrove
end Perennial
