/-
`storeTxnWrite.End` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnSteps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `tw.End()` ends the write transaction, its key-values released (`storeTxnWriteCore`: it
reads the `changes` slice's length only), its writer sealed or not: with a change, the pending
revision is committed (`currentRev++` and the batch transaction's write-back, under
`s.revMu`), certified (`idxCert` of `commitLog`); the transaction's tokens are the caller's
again (`storeReaderC`, with the reader's tag `Z`; 2026-10-13, unit 6a), and so is its revision
token if no revision was made (`pend = []`). `Unlock` takes the batch lock's invariant `P` (the
store's, `hookIs`) back; the writer's fragment is given back (D22 receiver epochs, S5b), and its pin at the committed log
(`writerPin`, M2's item 37). A commit takes the outer quarter of the committed log's authority and
gives it back at the committed log (`logQPre`/`logQPost`, unit W-K). The lock token may be the
one the lessor's delete from `Lease` left (`ld`, leases T3, 2026-10-25). The readers' statement (`storeReader`) is `specR` (`spec_R`, `ReaderSpecs.lean`).
(M4, track B, 2026-11-06; `Api/TxnSteps.lean`) The API's ghost state moves by the caller's step
(`endCb`): with no change at the check-in, with a change at the bump, under `s.revMu`, from the
writer's slot `Y` (the transaction's, `storeTxnWriteCoreY`) and the lock's slot at the
transaction's compaction revision; the writer's check-in excludes the frozen state by the caller's
`G` (given back). -/
abbrev mvcc.storeTxnWrite.End.spec : Prop :=
  ∀ (trace : Loc) (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (chs : GoSlice) (ps : List Loc) (sealed : Bool) (P : IProp GF) (f : val) (crev : Int)
    (Z : IProp GF) (ld : Bool) (Y G R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteCoreY tw s γ trace ilog pend chs ps sealed crev Z ld Y ∗ mvcc.hookIs γ P f ∗ P ∗
      mvcc.certOkNext γ ilog pend ∗ mvcc.logQPre γ ilog pend ∗
      G ∗ □ (mvcc.slotF γ ∗ G -∗ False) ∗ mvcc.endCb γ ilog pend crev Y R }}
    (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReaderC s γ ∗ □ Z ∗ mvcc.idxCert γ.idx (mvcc.commitLog ilog pend) ∗
      (if pend = [] then mvcc.revToken γ else iprop(True)) ∗ mvcc.logQPost γ ilog pend ∗
      mvcc.writerFrag γ ∗ mvcc.writerPin γ (mvcc.commitLog ilog pend) ∗ G ∗ R }}

end spec

end EtcdGrove
end Perennial
