/-
The writer side after `node.free`'s `Free` (U8, `notes/bbolt-proof-plan.md`): `wdbOK` is kept when
the writer frees the extent of a page of the committed tree (its slots are tree slots, so no `W`
slot moves; the synced freelist page's slots are not covered, so its ids stay apart).

`wdbOK_free` is a `sorry`: it is the store's bookkeeping (U3's `pendSlots_free`,
`pendingIds_free_perm` in `Model/Store` are the pieces), and it needs the writer's txid not to
wrap (`C.txid + 1 < 2 ^ 64`, so that its pending ids are not `committedPending`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section free
variable [GooseExts]

/-- **Freeing a page of the committed tree keeps `wdbOK`.** -/
theorem wdbOK_free (w : WDb) (id : w64) (pg : List w8) (hok : wdbOK w)
    (hpg : w.C.pages !! id.toNat = some pg)
    (hcan : w.fl.canFree w.wtxid id (1 + pageOverflow pg)) :
    wdbOK (w.withFl (w.fl.freePages w.wtxid id (1 + pageOverflow pg))) := by
  sorry

end free

end bbolt
end EtcdGrove
end Perennial
