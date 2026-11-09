/-
`tx.close()` (`tx.go`): the writer's statistics merged and `rwlock` released, or the reader removed; the fields cleared.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch (the freelist, integration I7).** Writer: 4d's `FreeCount`, `PendingCount`,
`EstimatedWritePageSize` under `flOwn` (`F.count < flMaxIds`: ids below the high-water mark),
results only stored in the statistics. Reader: `removeTx`, 4d's `RemoveReadonlyTXID` under
`metalock` (`flReaders fl (R.erase txid)`).
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

/-- (internal) the transaction done; a reader's token back. -/
def Tx.close.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView),
  {{ boltTx (GF := GF) tx γ 1 T }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"close")) (Val #()))
  {{ RET #(); txDone tx ∗ (if T.rw then emp else threadTok) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
