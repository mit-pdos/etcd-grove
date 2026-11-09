/-
`db.loadFreelist()` (`db.go`): once, `freelist.Read` of the synced page or `Init(freepages())`, published under `metalock` (the fork).
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch** (integration I7). `newFreelist` gives `flOwn fl FLState.empty ∗ flReaders fl []`.
No synced freelist: `DB.freepages` gives a fresh slice of `idsOk` ids, which 4d's `Init` takes
(the hash map's empty-`Init` premise holds: no page was free; none pending). A synced one:
`db.page(meta.Freelist())`'s bytes in the mapping, 4d's `Read` with the file's synced-freelist
clause (`fileHolds`: `freelistReadable`, ids distinct, from 2, below the high-water mark, so
`< flMaxIds`; the fresh freelist has nothing pending or free). Published under `metalock` with
`flReaders fl []`: `freepages`' own read transaction registered nothing (the freelist was still
`nil`), and `Open` still owns the database, so no other reader exists. `FreeCount` under
`F.count < flMaxIds`. This establishes the freelist invariants `Internal.lean` lists ("The
freelist's side"): every free page unreached by, or in the freelist page of, the current meta.
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

/-- (internal) the freelist loaded. -/
def DB.loadFreelist.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (M : DbM),
  {{ dbRaw (GF := GF) db γ M ∗ ⌜M.metaOk = true⌝ }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"loadFreelist")) (Val #()))
  {{ RET #(); dbRaw db γ M }}

end spec

end Bbolt
end EtcdGrove
end Perennial
