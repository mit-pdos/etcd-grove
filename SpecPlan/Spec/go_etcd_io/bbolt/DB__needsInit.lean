/-
`db.needsInit(size)` (`db.go`, the fork's crash-safe `init`): whether `Open` initializes the file: an empty one, or (writable)
one of at most four pages whose every byte is zero or `initImage`'s, not that whole image. (Until 2026-11-25 `metasZero`.)
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

/-- (internal) the answer, or a read error. -/
def DB.needsInit.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (M : DbM) (sz : w64),
  {{ dbRaw (GF := GF) db γ M }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"needsInit")) (Val #sz))
  {{ (b : Bool) (err : GoInterface), RET (PairV #b #err); dbRaw db γ M }}

end spec

end Bbolt
end EtcdGrove
end Perennial
