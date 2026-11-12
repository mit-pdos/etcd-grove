/-
`compareToPath` (`txn.go`). Lean-first; see `TxnRun.lean`.
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
open mvcc.api (MvccState MTxn MvccReachable MvccName MvccStorage mvccN mvccLeases)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn

/-- `compareToPath(rv, rt)` on a read transaction at `σ`: the request's path (`txnPath`) at its
state, in a fresh slice.

(Strict M1, 2026-11-05: over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean` drafts it.) -/

abbrev txn.compareToPath.spec : Prop :=
  ∀ (t : GoInterface) (γ : MvccName) (trace : Loc) (te : Bool) (σ : MvccState) (rt : Loc)
    (tm : TxnModel),
  {{ pkgInit ∗ mvcc.api.mvccTxn t γ trace (.read σ) ∗ traceutil.ownTrace trace te ∗
      ⌜txn.Reach σ⌝ ∗ txn.txnRequestIs rt tm }}
    (App (App (Val (@! txn.compareToPath)) (Val #t)) (Val #rt))
  {{ (sl : GoSlice), RET #sl; mvcc.api.mvccTxn t γ trace (.read σ) ∗ traceutil.ownTrace trace te ∗
      sl ↦* txn.txnPath (mvcc.stateAfter σ.log) tm ∗ ownSliceCap Bool sl (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
