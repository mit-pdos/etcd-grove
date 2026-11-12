/-
`b.maxInlineBucketSize()` (`bucket.go`): `pageSize / 4`.
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

/-- (internal) `1024`. -/
def Bucket.maxInlineBucketSize.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (gs : List Nat),
  {{ boltTx (GF := GF) tx γ q T ∗ bktH tx γ b p gs }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"maxInlineBucketSize")) (Val #()))
  {{ (z : w64), RET #z; boltTx tx γ q T ∗ ⌜uint.nat z = 1024⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
