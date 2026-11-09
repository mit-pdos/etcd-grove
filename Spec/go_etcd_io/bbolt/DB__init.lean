/-
`db.init()` (`db.go`, the fork's crash-safe `init`): writes pages 2-3 and zero metas, syncs, then the metas, syncs. Users: `Open` on a fresh file.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
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
  {{ dbRaw (GF := GF) db γ M }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"init")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ M' : DbM, dbRaw db γ M' ∗ ⌜err = GoInterface.nil → M'.metaOk = true⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
