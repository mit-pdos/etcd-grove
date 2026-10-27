/-
`etcdserverpb.NewLoggableTxnRequest`: the trust boundary (`api/etcdserverpb/raft_internal_stringer.go`,
names-only). Lean-first (no Rocq counterpart); unit P4 (2026-10-14), for the server's read-only
`Txn` (`txn.WarnOfExpensiveReadOnlyTxnRequest` logs the request through it).

`NewLoggableTxnRequest(r)` returns `&txnRequestStringer{r}` as a `fmt.Stringer`, whose `String()`
formats the request's comparisons and operations (values redacted: `newLoggableValueCompare`,
`newLoggablePutRequest`; the others by protobuf's `String()`), reading the request
(`txnRequestIs`, read-only; the messages' internal state is not modelled, as for `proto.Size`).
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
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `NewLoggableTxnRequest(r)` of the transaction request `r` (`txnRequestIs`): a stringer whose
`String()` returns (`stringerOk`). -/
abbrev NewLoggableTxnRequest.spec : Prop :=
  ∀ (r : Loc) (t : TxnModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      txn.txnRequestIs r t }}
    (App (Val (@! etcdserverpb.NewLoggableTxnRequest)) (Val #r))
  {{ (s : GoInterface), RET #s; txn.stringerOk s }}

end spec

end EtcdGrove
end Perennial
