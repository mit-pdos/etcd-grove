/-
`storeTxnWrite.Range` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `tw.Range(ctx, key, end, ro)`: the write transaction's range read sees its own pending
changes. It is `rangeKeys` at the transaction's revision (`writeRev`: the pending one once it
has a change, else the committed log's last) of the committed log with the pending revision
appended (`ilog ++ [pend]`; with no change the empty revision changes nothing), read from the
index by the writer and from the bucket through the batch transaction, which sees its own
puts. -/
abbrev mvcc.storeTxnWrite.Range.spec : Prop :=
  ∀ (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key endk : GoSlice) (k e : GoString)
    (ro : RangeOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteIs tw s γ ilog pend ∗ context.isContext ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
    (App (App (App (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      mvcc.storeTxnWriteIs tw s γ ilog pend ∗
      mvcc.rangeOutcome r err (ilog ++ [pend]) (W64 ((mvcc.writeRev ilog pend : Nat) : Int))
        (decide (endk = slice.nil)) k e ro }}

end spec

end EtcdGrove
end Perennial
