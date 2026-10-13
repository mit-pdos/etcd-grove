/-
`storeTxnCommon__Range` (`kvstore_txn.go`). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange

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

/-- `tr.Range(ctx, key, end, ro)` is `rangeKeys` at the transaction's revision (at
`context.TODO()`, `todo`, no context error), at the compaction revision `crev` the transaction
observed (its hold of `s.mu`, `muHeld` at `crev`, given back: `ErrCompacted` below it, the
uncompacted outcome at or above it, `rangeOutcomeC`; 2026-10-13, unit 6a), under the
transaction's reader (`txReader`, kept). The frozen statement (a store never compacted, `crev =
-1`: `rangeOutcome`) is `specFrozen`, a corollary (`spec_frozen`, `FrozenSpecs.lean`). -/
abbrev mvcc.storeTxnCommon.Range.spec : Prop :=
  ∀ (tr s trace ti : Loc) (rt : GoInterfaceOk) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool)
    (key endk : GoSlice) (k e : GoString) (ro : RangeOptions) (crev : Int) (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeTxnReadIs tr s rt trace γ log rev crev Z ∗ mvcc.txReader γ rt log ∗
      s.[store, go!"kvindex"] ↦□ (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      mvcc.idxReader ti γ.idx ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e ∗
      mvcc.muHeld s γ crev }}
    (App (App (App (App (Val (mvcc.txCommon tr @!! go.GoType.PointerType storeTxnCommon.ty @!!
      go!"Range")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗
      mvcc.idxReader ti γ.idx ∗ mvcc.muHeld s γ crev ∗ mvcc.txReader γ rt log ∗
      mvcc.rangeOutcomeC r err log rev crev (decide (endk = slice.nil)) k e ro }}

end spec

end EtcdGrove
end Perennial
