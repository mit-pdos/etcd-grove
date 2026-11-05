/-
`applyCompare` (`txn.go`). Lean-first; see `TxnRun.lean`.
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

/-- `applyCompare(rv, c)` on a read transaction at `σ`: `cmpHolds` at its state.

(Strict M1, 2026-11-05: restated over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean`
drafts it, frozen; `notes/mvcc-api-clients/clients-txn.md`.) -/
abbrev txn.applyCompare.spec : Prop :=
  ∀ (t : GoInterface) (γ : MvccName) (trace : Loc) (te : Bool) (σ : MvccState) (c : Loc)
    (cm : CmpModel),
  {{ pkgInit ∗ mvcc.api.mvccTxn t γ trace (.read σ) ∗ traceutil.ownTrace trace te ∗
      ⌜txn.Reach σ⌝ ∗ txn.compareIs c cm }}
    (App (App (Val (@! txn.applyCompare)) (Val #t)) (Val #c))
  {{ RET #(cmpHolds (mvcc.stateAfter σ.log) cm); mvcc.api.mvccTxn t γ trace (.read σ) ∗
      traceutil.ownTrace trace te }}

end spec

end EtcdGrove
end Perennial
