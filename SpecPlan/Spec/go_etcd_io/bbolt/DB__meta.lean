/-
`db.meta()` (`db.go`): the valid meta of the higher txid (panics if neither is valid: excluded by `metaOk`).
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Internal

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

/-- (internal) the current meta. -/
def DB.meta.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (M : DbM),
  {{ dbRaw (GF := GF) db γ M ∗ ⌜M.metaOk = true⌝ }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"meta")) (Val #()))
  {{ (m : Loc), RET #m; dbRaw db γ M }}

end spec

end Bbolt
end EtcdGrove
end Perennial
