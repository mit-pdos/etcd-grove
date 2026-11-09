/-
`db.getPageSizeFromSecondMeta()` (`db.go`): page 1's meta, at offsets the fork reads only after page 0 was read.
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

/-- (internal) its page size if valid. -/
def DB.getPageSizeFromSecondMeta.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (M : DbM),
  {{ dbRaw (GF := GF) db γ M }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"getPageSizeFromSecondMeta")) (Val #()))
  {{ (z : w64) (ok : Bool) (err : GoInterface), RET (PairV #z (PairV #ok #err)); dbRaw db γ M ∗ ⌜ok = true → uint.nat z = 4096⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
