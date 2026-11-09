/-
`b.Cursor()` (`bucket.go`): a new cursor over the bucket (`IncCursorCount`, atomic).

**Users.** The backend's ranges (`batch_tx.go:203`, `read_tx.go:117`: cursors made under the read
transaction's lock, moved concurrently by readers, each its own), `ForEach`. Snippets:
`ReqBackendBatch`, `ReqBackendRead`. **Proof sketch.** Allocate the `Cursor` with an empty stack.
**Changes.** Over paths; the cursor records the handle's generations.
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

/-- `b.Cursor()`: an unpositioned cursor over the bucket at `p`. -/
def Bucket.Cursor.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (gs : List Nat),
  {{ boltTx (GF := GF) tx γ q T ∗ bktH tx γ b p gs ∗ ⌜T.gens p = gs⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Cursor")) (Val #()))
  {{ (c : Loc), RET #c; boltTx tx γ q T ∗ boltCur tx γ c p gs T none }}

end spec

end Bbolt
end EtcdGrove
end Perennial
