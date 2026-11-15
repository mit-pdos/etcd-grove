/-
`db.growSize(mmapSize, growSize)` (`db.go`).
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

/-- (internal) the size `grow` truncates to. -/
def DB.growSize.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (ns : Bool) (a g : w64),
  {{ isBolt (GF := GF) db γ ns }}
    (App (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"growSize")) (Val #a)) (Val #g))
  {{ (z : w64), RET #z; True }}

end spec

end Bbolt
end EtcdGrove
end Perennial
