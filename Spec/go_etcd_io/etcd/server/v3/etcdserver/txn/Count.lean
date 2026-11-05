/-
`Count` (`range.go`): the number of keys in a range.
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
open mvcc.api (MvccState MTxn MvccReachable MvccName MvccStorage mvccN mvccLeases)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn

/-- **`Count(ctx, lg, kv, key, rangeEnd, revision)`**: as today, at the state of the caller's
update.

(Strict M1, 2026-11-05: restated over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean`
drafts it, frozen; `notes/mvcc-api-clients/clients-txn.md`.) -/
abbrev txn.Count.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg : Loc) (kv : GoInterface)
    (γ : MvccName) (key rangeEnd : GoSlice) (k e : GoString) (revision : w64) (ot : Option Loc)
    (te : Bool) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ mvcc.api.isMvcc kv γ ∗ threadTok ∗ key ↦*□ k ∗ rangeEnd ↦*□ e ∗
      mvcc.txnCtx ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗
      ⌜lg ≠ null⌝ ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ ∗ txn.readAU γ Q }}
    (App (App (App (App (App (App (Val (@! txn.Count)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #kv)) (Val #key)) (Val #rangeEnd)) (Val #revision))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      threadTok ∗ ∃ σ : MvccState, Q σ ∗ ⌜txn.Reach σ⌝ ∗
        ((⌜err = GoInterface.nil ∧ sint.Z revision ≤ (σ.rev : Int) ∧
            n = W64 ((rangeIn (mvcc.stateAt σ.log (sint.nat (mvcc.rangeRev (W64 (σ.rev : Int)) revision)))
              (txn.countOp k (txn.rangeEndOf rangeEnd e) revision)).length : Int)⌝) ∨
         (⌜(σ.rev : Int) < sint.Z revision ∧ n = W64 0⌝ ∗ ∃ ef : GoInterfaceOk,
            globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∨
         (⌜sint.Z revision ≤ (σ.rev : Int) ∧
            sint.Z (mvcc.rangeRev (W64 (σ.rev : Int)) revision) < σ.crev ∧ n = W64 0⌝ ∗
            ∃ ec : GoInterfaceOk,
            globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝)) }}

end spec

end EtcdGrove
end Perennial
