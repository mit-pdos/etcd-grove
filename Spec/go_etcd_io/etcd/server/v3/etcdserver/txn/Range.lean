/-
`Range` (`range.go`): a range request on the store.
Lean-first; see `InvRange.lean`, `RangeModel.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiVocab

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc
open mvcc.api (MvccState MTxn MvccReachable MvccName BkRef mvccN mvccLeases)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn

/-- **`Range(ctx, lg, kv, r, withTotalCount)`**: a read transaction at the state `σ` of the
caller's update (`Q σ`), and `rangeResult` there (the sort's premise from `Txn.Range`'s
`stateOk`). Callers: the apply thread (its `Q` pins `σ.log`
to its log), the server's read path (its `Q` gives the floor and its model of `σ.log`).

(Strict M1, 2026-11-05: restated over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean`
drafts it, frozen; `notes/mvcc-api-clients/clients-txn.md`.) -/
abbrev txn.Range.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg : Loc)
    (kv : GoInterface) (γ : MvccName) (r : Loc) (o : OpFull) (withTotal : Bool) (ot : Option Loc)
    (te : Bool) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ mvcc.api.isMvcc kv γ ∗ threadTok ∗ txn.rangeRequestIs r o ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗
      (if nd then mvcc.neverDone cd else iprop(True)) ∗ ⌜lg ≠ null⌝ ∗ ⌜txn.validSortTarget o⌝ ∗
      txn.readAU γ Q }}
    (App (App (App (App (App (Val (@! txn.Range)) (Val #(GoInterface.ok ctx))) (Val #lg)) (Val #kv))
      (Val #r)) (Val #withTotal))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      threadTok ∗ ⌜trace ≠ null⌝ ∗ (∃ te' : Bool, traceutil.ownTrace trace te') ∗
      ⌜∀ t0, ot = some t0 → te = false → trace = t0⌝ ∗
      ∃ σ : MvccState, Q σ ∗ ⌜txn.Reach σ⌝ ∗
        txn.rangeResult resp err σ.log (W64 (σ.rev : Int)) σ.crev o withTotal ∗
        txn.rangeHdr resp err ∗
        ⌜nd = true → err = GoInterface.nil ∨ sint.Z (W64 (σ.rev : Int)) < sint.Z o.base.rev ∨
          sint.Z (mvcc.rangeRev (W64 (σ.rev : Int)) o.base.rev) < σ.crev⌝ }}

end spec

end EtcdGrove
end Perennial
