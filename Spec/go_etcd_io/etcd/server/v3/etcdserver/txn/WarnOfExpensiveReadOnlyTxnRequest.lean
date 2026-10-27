/-
`txn.WarnOfExpensiveReadOnlyTxnRequest` (`util.go`, translated: unit P4, 2026-10-14; it was a
trust-boundary axiom, "it returns" with no premise, false of the code: unit P1). Lean-first (no
Rocq counterpart); the request path (`notes/decisions.md`, "The request path").

When the transaction took longer than `d`, it makes the request's stringer
(`pb.NewLoggableTxnRequest`, which reads the request: `txnRequestIs`), formats the response
(unless nil: each range's `GetKvs()` length, `txnRespShow`, and `proto.Size`) and warns through
`lg` (`warnOfExpensiveGenericRequest`). So: a logger, the request, and a nil response or its
`Responses` (read-only) and `proto.Size` of it (`sizeOk`, lent `P`: the server's `Txn` lends its
header's id fields). The server's read-only `Txn` passes a response even on the context's error
(partly filled: `txn.Txn.specRead`), which these premises cover (`roTxnRespRd`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvWarn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `WarnOfExpensiveReadOnlyTxnRequest(lg, d, now, r, resp, err)`, with a logger, the request `r`
(`txnRequestIs`), and a nil response or one whose responses it can read (`txnRespShow`) and
`proto.Size` of which returns lent `P`: it returns, `P` given back. -/
abbrev txn.WarnOfExpensiveReadOnlyTxnRequest.spec : Prop :=
  ∀ (lg : Loc) (d : time.Duration) (now : time.Time) (r : Loc) (t : TxnModel) (resp : Loc)
    (err : GoInterface) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ ⌜lg ≠ null⌝ ∗
      txn.txnRequestIs r t ∗ P ∗
      (⌜resp = null⌝ ∨ txn.txnRespShow resp ∗
        txn.sizeOk (interface.mkOk (go.GoType.PointerType etcdserverpb.TxnResponse.ty) #resp) P) }}
    (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfExpensiveReadOnlyTxnRequest)) (Val #lg)) (Val #d))
      (Val #now)) (Val #r)) (Val #resp)) (Val #err))
  {{ RET #(); P }}

end spec

end EtcdGrove
end Perennial
