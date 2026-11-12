/-
`b.Tx()` (`bucket.go`). **Users.** None in etcd. **Proof sketch.** `b.tx`, immutable (a persistent
share in `bktH`). **Changes.** New.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Api

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

/-- `b.Tx()`: the handle's transaction. -/
def Bucket.Tx.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (b : Loc) (p : BPath) (gs : List Nat),
  {{ bktH (GF := GF) tx γ b p gs }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Tx")) (Val #()))
  {{ RET #tx; True }}

end spec

end Bbolt
end EtcdGrove
end Perennial
