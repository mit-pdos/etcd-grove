/-
`db.fileSize()` (`db.go`): `Stat` of the file.
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

/-- (internal) its size, or an error. -/
def DB.fileSize.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (M : DbM),
  {{ dbRaw (GF := GF) db γ M }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"fileSize")) (Val #()))
  {{ (z : w64) (err : GoInterface), RET (PairV #z #err); dbRaw db γ M ∗ ⌜err = GoInterface.nil → uint.nat z = M.fileSz⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
