/-
`db.mmap(minsz)` (`db.go`): under `mmaplock`'s writer side, `mmapUnlocked`.
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

/-- (internal) mapped at least `minsz`, or an error (then unmapped). -/
def DB.mmap.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (M : DbM) (minsz : w64),
  {{ dbRaw (GF := GF) db γ M }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"mmap")) (Val #minsz))
  {{ (err : GoInterface), RET #err; ∃ M' : DbM, dbRaw db γ M' ∗ ⌜err = GoInterface.nil → uint.nat minsz ≤ M'.dataSz ∧ M'.metaOk = true⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
