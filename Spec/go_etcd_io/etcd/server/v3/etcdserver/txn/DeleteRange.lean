/-
`txn.DeleteRange` (delete.go). Lean-first (no Rocq counterpart); see `Proof/.../etcdserver/txn/Write.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Write

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- **`DeleteRange(ctx, lg, kv, dr)`**: the delete request `o` as one write transaction, opened
with a revision token, at a committed log `ilog` the caller's other tokens and certificate pin
(`Pinned`; at the sole writer, its own log), with fewer than `2^63` keys. The keys of the
request's range at `ilog`'s state deleted (`delChanges`; the client's delete there:
`stateAfter_commit_delete`): the committed log `commitLog` (no revision, the token back, if
nothing was deleted), the response with their number, the revision (`writeRev`: the new one, or
`ilog`'s last if nothing was deleted) and (`PrevKv`) the deleted key-values; or, with `PrevKv`,
the range read's context error (`ctx` done): nothing deleted, the token back. The trace is not
`nil`. The write transaction runs under the store's batch lock by the critical-section contract
(`csContract P f Pre Q Post`, the store's hook `hookIs γ P f`): `Post`. At a context never
canceled (`nd`: `neverDone`), no context error (2026-10-12: for the apply package's backend). -/
abbrev txn.DeleteRange.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg : Loc) (kv : GoInterface)
    (s : Loc) (γ : mvcc.StoreNames) (dr : Loc) (o : OpFull) (m : Nat) (log₀ : mvcc.Log)
    (P Pre Q Post : IProp GF) (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ txn.isKV kv s γ ∗ mvcc.storeReader s γ ∗ mvcc.revToken γ ∗
      ownToks γ.revs m ∗ mvcc.idxCert γ.idx log₀ ∗ txn.deleteRangeRequestIs dr o ∗
      mvcc.txnCtx ctx cd ∗ (if nd then mvcc.neverDone cd else iprop(True)) ∗
      ⌜∀ ilog : mvcc.Log, txn.Pinned log₀ m ilog → (mvcc.stateAfter ilog).length < 2 ^ 63⌝ ∗
      mvcc.csContract P f Pre Q Post ∗ mvcc.hookIs γ P f }}
    (App (App (App (App (Val (@! txn.DeleteRange)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #kv)) (Val #dr))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      mvcc.storeReader s γ ∗ ownToks γ.revs m ∗ ⌜trace ≠ null⌝ ∗ Post ∗
      ∃ ilog : mvcc.Log, ⌜txn.Pinned log₀ m ilog ∧ ilog ≠ []⌝ ∗
        ((⌜err = GoInterface.nil⌝ ∗
            txn.deleteRangeResponseIs resp
              (W64 ((mvcc.writeRev ilog (txn.delChanges (mvcc.stateAfter ilog) o) : Nat) : Int))
              (rangeIn (mvcc.stateAfter ilog) o).length
              (if o.base.prevKV then rangeIn (mvcc.stateAfter ilog) o else []) ∗
            mvcc.idxCert γ.idx (mvcc.commitLog ilog (txn.delChanges (mvcc.stateAfter ilog) o)) ∗
            (if txn.delChanges (mvcc.stateAfter ilog) o = [] then mvcc.revToken γ else True)) ∨
         (⌜err ≠ GoInterface.nil ∧ o.base.prevKV = true ∧ resp = null ∧ nd = false⌝ ∗
            mvcc.revToken γ ∗ mvcc.idxCert γ.idx ilog)) }}

end spec

end EtcdGrove
end Perennial
