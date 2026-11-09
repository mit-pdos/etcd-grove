/-
`db.loadFreelist()` (`db.go`): once, `freelist.Read` of the synced page or `Init(freepages())`, published under `metalock` (the fork).
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
