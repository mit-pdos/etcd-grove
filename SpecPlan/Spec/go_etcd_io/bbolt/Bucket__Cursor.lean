/-
`b.Cursor()` (`bucket.go`): a new cursor over the bucket (`IncCursorCount`, atomic).

**Users.** The backend's ranges (`batch_tx.go:203`, `read_tx.go:117`: cursors made under the read
transaction's lock, moved concurrently by readers, each its own), `ForEach`. Snippets:
`ReqBackendBatch`, `ReqBackendRead`. **Proof sketch.** Allocate the `Cursor` with an empty stack.
**Changes.** Over paths; the cursor records its handle.
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** Takes only the persistent
`bktH` (it reads `b.tx` alone; `bktOwn_bktH` gives it from a write transaction's token), in place of
`bktH … gs` and the generation check; the cursor names its handle `b`, and its moves take the handle
premise (the per-path generation counter it replaces was unobservable state, redundant with
ownership).
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

/-- `b.Cursor()`: an unpositioned cursor over the bucket at `p`. -/
def Bucket.Cursor.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath),
  {{ boltTx (GF := GF) tx γ q T ∗ bktH tx γ b p }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Cursor")) (Val #()))
  {{ (c : Loc), RET #c; boltTx tx γ q T ∗ boltCur tx γ c b p T none }}

end spec

end Bbolt
end EtcdGrove
end Perennial
