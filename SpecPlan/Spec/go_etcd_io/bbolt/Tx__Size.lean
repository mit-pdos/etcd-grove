/-
`tx.Size()` (`tx.go`): `int64(tx.meta.Pgid()) * int64(tx.db.pageSize)`, the database's size as of
the transaction.

**Users.** `backend.Snapshot` (`backend.go:392`, the snapshot's size), defrag (`:603`). Snippet:
`ReqSnapshot`. **Proof sketch.** The transaction's meta's high-water mark times `4096`: the
mapping covers `hwm` pages and is at most `maxMapSize = 2 ^ 48 - 1` bytes (`mmapSize` refuses more:
an error of the commit that would grow past it), so the product is below `2 ^ 48`.
**Changes.** Strengthened: the size is `txSize`'s (`boltTx_size`: below `2 ^ 48`, 2d's need of
`[0, 2 ^ 62)`; `WriteTo`'s image length: 4a's item 7, the maintenance service's `RemainingBytes`).
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

/-- `tx.Size()`: the transaction's size `n` (`txSize`: below `2 ^ 48`, `WriteTo`'s length). -/
def Tx.Size.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (n : w64),
  {{ boltTx (GF := GF) tx γ q T ∗ txSize tx n }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Size")) (Val #()))
  {{ RET #n; boltTx tx γ q T }}

end spec

end Bbolt
end EtcdGrove
end Perennial
