/-
`db.init()` (`db.go`, the fork's crash-safe `init`): writes pages 2-3 and zero metas, syncs, then the metas, syncs. Users: `Open` on a fresh file.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch** (integration I7). `make([]byte, 4 · pageSize)`; per meta page, `pageInBuffer` (its
bound: `4 · 4096`), 4d's `Page.SetId`/`SetFlags`, `Page.Meta` and the `Meta` setters through
`meta_view` (`metaLoc p`), `NewInBucket(3, 0)`, `Sum64`/`SetChecksum` (so `metaValid` by
`metaValid_summed`: txids 0 and 1, the second the current, so the file invariant's txid `≥ 1`);
the freelist page (count 0) and the empty leaf by `SetId`/`SetFlags`/`SetCount`; the two writes
and syncs over OsFs (the meta pages written last, after the pages they point at are synced).

**Changes** (integration I7): the premise `M.pageSize = 4096` (`Open` sets it from the default,
4d's `BboltCommon.init.spec`, D13); a page size of 0 makes `pageInBuffer` panic.
-/
module

public import Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) the file laid out as the empty database (every crash image `Data.empty`), or an error. -/
def DB.init.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (M : DbM),
  {{ dbRaw (GF := GF) db γ M ∗ ⌜M.pageSize = 4096⌝ }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"init")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ M' : DbM, dbRaw db γ M' ∗ ⌜err = GoInterface.nil → M'.metaOk = true⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
