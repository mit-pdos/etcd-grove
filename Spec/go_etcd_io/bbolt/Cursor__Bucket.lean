/-
`c.Bucket()` (`cursor.go`): the cursor's bucket handle. **Users.** None in etcd.
**Proof sketch.** `c.bucket`. **Changes.** New.
-/
module

public import Spec.go_etcd_io.bbolt.Api

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

/-- `c.Bucket()`: the handle of the cursor's bucket. -/
def Cursor.Bucket.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (p : BPath) (gs : List Nat) (pos : Option Nat),
  {{ boltCur (GF := GF) tx γ c p gs T pos }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Bucket")) (Val #()))
  {{ (b : Loc), RET #b; boltCur tx γ c p gs T pos ∗ bktH tx γ b p gs }}

end spec

end Bbolt
end EtcdGrove
end Perennial
