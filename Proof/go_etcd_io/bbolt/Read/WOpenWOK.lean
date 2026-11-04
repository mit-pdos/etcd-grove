/-
The writer's opened buckets, well-formedness (U6e, `notes/bbolt-proof-plan.md`): opening a nested
bucket (`bktOpened`'s state, `WX.addBkt` over the parent's cache update) keeps `wOK` and the
writer's data.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WOpenH
public import Proof.go_etcd_io.bbolt.Read.WOpenOK

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace WOpen

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wok
variable [GooseExts]

/-- **Opening a nested bucket keeps `wOK` and the data**: the parent `bl`'s cache gains
`nb ↦ c`, the fresh bucket `c` (record `C`, `openedRec` of the entry's value) is added, live, a
handle. -/
theorem wOK_bktOpened (X : WX) (bl c : Loc) (B C : BRec) (w : WEntry) (nb : List w8) (g : Nat)
    (hok : wOK X) (hB : X.t.bs !! bl = some B) (hw : w ∈ X.allEnts bl) (hk : w.key = nb)
    (hf : isBktFlag w.flags) (hbm : B.bm !! nb = none) (hbo : X.t.bobjs !! c = none)
    (hrec : openedRec B.bv.tx' w.value w.vs C)
    (hbv : bvalOK X.v.pages X.t.mv.pgid'.toNat w.value) (hent : entryIn X.v B nb w.value)
    (htk : inBucketRoot w.value ≠ 0 → treeKeys X.v.pages (inBucketRoot w.value) none none) :
    wOK ((X.setBkt bl { B with bm := B.bm.insert nb c }).addBkt c C (nb, g)) ∧
      wtxData ((X.setBkt bl { B with bm := B.bm.insert nb c }).addBkt c C (nb, g)) = wtxData X := by
  sorry

end wok

end WOpen

end bbolt
end EtcdGrove
end Perennial
