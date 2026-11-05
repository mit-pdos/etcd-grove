/-
`checkRange` (`range.go`): the revision check of a range in a transaction.
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

/-- `checkRange(rv, req)` on a read transaction at `σ`.

(Strict M1, 2026-11-05: restated over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean`
drafts it, frozen; `notes/mvcc-api-clients/clients-txn.md`. With `⌜txn.Reach σ⌝` added, decided by
the coordinator, 2026-11-05: `FirstRev`'s `W64 σ.crev` is `σ.crev` only for a reachable state.) -/
abbrev txn.checkRange.spec : Prop :=
  ∀ (t : GoInterface) (γ : MvccName) (trace : Loc) (σ : MvccState) (req : Loc) (o : OpFull),
  {{ pkgInit ∗ mvcc.api.mvccTxn t γ trace (.read σ) ∗ ⌜txn.Reach σ⌝ ∗ txn.rangeRequestIs req o }}
    (App (App (Val (@! txn.checkRange)) (Val #t)) (Val #req))
  {{ (err : GoInterface), RET #err; mvcc.api.mvccTxn t γ trace (.read σ) ∗
      txn.checkRangeErr (W64 (σ.rev : Int)) σ.crev o err }}

end spec

end EtcdGrove
end Perennial
