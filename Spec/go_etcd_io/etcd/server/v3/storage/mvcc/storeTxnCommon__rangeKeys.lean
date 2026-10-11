/-
`storeTxnCommon__rangeKeys` (`kvstore_txn.go`). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `txc.rangeKeys(ctx, key, end, curRev, ro)` of a transaction at revision `curRev` of the log
`log` answers `rangeOutcome`: the index's answers at that revision, with the key-values the
bucket holds for them. What it uses of the `storeTxnCommon` at `txc`: its fields `s`, `tx` and
`trace` (at any fraction, given back); of its reader `tx`: a reader (`keyReader`) of a bucket
`m` holding `log`'s, with the reader's own resource `R` (given back); of the index: what the
transaction knows of it (`idxKnows`: a committed log's certificate for a read transaction,
the writer's handle for a write transaction, with its pending revision; given back), and
`curRev` a revision of `log`. -/
abbrev mvcc.storeTxnCommon.rangeKeys.spec : Prop :=
  ∀ (txc s trace ti : Loc) (rt : GoInterfaceOk) (dq : DFrac) (m : mvcc.Bucket) (R : IProp GF)
    (γ : mvcc.StoreNames) (kn : mvcc.IdxKnow) (log : mvcc.Log) (rev : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key endk : GoSlice) (k e : GoString)
    (ro : RangeOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗
      txc.[storeTxnCommon, go!"s"] ↦{dq} s ∗
      txc.[storeTxnCommon, go!"tx"] ↦{dq} (GoInterface.ok rt : GoInterface) ∗
      txc.[storeTxnCommon, go!"trace"] ↦{dq} trace ∗
      mvcc.keyReader rt m R ∗ R ∗ ⌜GMap.Subseteq (mvcc.bucketMap log) m⌝ ∗
      mvcc.idxKnows γ.idx kn ∗ ⌜kn.log = log⌝ ∗ ⌜log ≠ []⌝ ∗
      ⌜0 ≤ sint.Z rev ∧ sint.Z rev < log.length⌝ ∗
      s.[store, go!"kvindex"] ↦□ (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      mvcc.idxReader ti γ.idx ∗ context.isContext ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
    (App (App (App (App (App (Val (txc @!! go.GoType.PointerType storeTxnCommon.ty @!!
      go!"rangeKeys")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #rev)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      txc.[storeTxnCommon, go!"s"] ↦{dq} s ∗
      txc.[storeTxnCommon, go!"tx"] ↦{dq} (GoInterface.ok rt : GoInterface) ∗
      txc.[storeTxnCommon, go!"trace"] ↦{dq} trace ∗
      R ∗ mvcc.idxKnows γ.idx kn ∗ mvcc.idxReader ti γ.idx ∗
      mvcc.rangeOutcome r err log rev (decide (endk = slice.nil)) k e ro }}

end spec

end EtcdGrove
end Perennial
