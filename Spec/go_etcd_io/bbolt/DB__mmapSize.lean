/-
`db.mmapSize(size)` (`db.go`): doubling to 1 GiB, then 1 GiB steps, page-aligned, at most `MaxMapSize`.
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

/-- (internal) a mapping size at least `size` and at most `2 ^ 48 - 1`, or an error above it. -/
def DB.mmapSize.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (M : DbM) (sz : w64),
  {{ dbRaw (GF := GF) db γ M }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"mmapSize")) (Val #sz))
  {{ (z : w64) (err : GoInterface), RET (PairV #z #err); dbRaw db γ M ∗ ⌜err = GoInterface.nil → uint.nat z < 2 ^ 48⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
