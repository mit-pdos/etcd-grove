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

/-- **A view value of the committed tree is a `bvalS`** over a page map `P` agreeing with the
view, at a mark above the committed one; its slots are its `bucketCovers`. -/
theorem bvalS_view {X : WX} {C : CommitSt} (hcok : treeOK C) (hcp : X.v.pages = C.pages)
    {hwm hwm' : Nat} (hch : C.hwm ≤ hwm) {P : Pages}
    (hag : ∀ x pg, X.v.pages !! x = some pg → P !! x = some pg) {v : List w8}
    (hv : bvalOK X.v.pages hwm' v)
    (hk : inBucketRoot v ≠ 0 → treeKeys X.v.pages (inBucketRoot v) none none) :
    ∃ S, bvalS P hwm v S ∧ ∀ s, s ∈ pgSlots P S ↔ bucketCovers X.v.pages v s := by
  sorry

/-- **An uncached nested bucket's value in a leaf node of the root** is a `bvalS`. -/
theorem bvalS_uncached {X : WX} {C : CommitSt} (hok : wOKR X) (hcok : treeOK C)
    (hcp : X.v.pages = C.pages) {hwm : Nat} (hch : C.hwm ≤ hwm) {P : Pages}
    (hag : ∀ x pg, X.v.pages !! x = some pg → P !! x = some pg)
    {R : BRec} (hR : X.t.bs !! X.rl = some R) {l : Loc} {r : NRec} (hr : R.ns !! l = some r)
    (hl : r.nv.isLeaf' = true) {w : WEntry} (hw : w ∈ r.ws) (hb : isBktFlag w.flags)
    (hnc : R.bm !! w.key = none) :
    ∃ S, bvalS P hwm w.value S ∧ ∀ s, s ∈ pgSlots P S ↔ bucketCovers X.v.pages w.value s := by
  sorry

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
  sorry

end val

end Spill

end bbolt
end EtcdGrove
end Perennial
