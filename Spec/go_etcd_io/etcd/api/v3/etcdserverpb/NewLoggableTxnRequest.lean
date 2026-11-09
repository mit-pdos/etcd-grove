/-
`etcdserverpb.NewLoggableTxnRequest(r)` (`api/etcdserverpb/raft_internal_stringer.go`, generated
package, names only here: assumed).

Users: `txn.WarnOfExpensiveReadOnlyTxnRequest` (`server/etcdserver/txn/util.go`; the server's
read-only `Txn` logs the request through it), `v3rpc`'s `logUnaryRequestStats`
(`server/etcdserver/api/v3rpc/interceptor.go:163`).

Why true: it returns `&txnRequestStringer{r}` as a `fmt.Stringer`, whose `String()` formats the
comparisons and operations (values redacted: `newLoggableValueCompare`, `newLoggablePutRequest`;
the others by protobuf's `String()`), reading the request only. The stringer holds the caller's
share of the request until it gives it back (`stringerAt`'s realization).

Changes: verify-round: restored (A6 completeness F6: dropped from the old tree,
`specs-ref/Spec/go_etcd_io/etcd/api/v3/etcdserverpb/NewLoggableTxnRequest.lean`, whose
`txnRequestIs` is now `msgAt` at any share), returning 3h's `stringerAt` (not persistent: it holds
the share) in place of txn's provisional persistent `stringerOk`.
Margin: none (the string's content is not modelled: its users log it).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Stringer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServerPb

open Iris Iris.BI
open go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `NewLoggableTxnRequest(r)` of a transaction request held at `dq`: a stringer holding that share,
which it gives back. -/
def NewLoggableTxnRequest.spec : Prop :=
  ∀ (r : Loc) (dq : DFrac) (c : Proto.Content),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      Proto.msgAt etcdserverpb.TxnRequest.ty r dq c }}
    (App (Val (@! etcdserverpb.NewLoggableTxnRequest)) (Val #r))
  {{ (s : GoInterface), RET #s; stringerAt s ∗
      (stringerAt s -∗ Proto.msgAt etcdserverpb.TxnRequest.ty r dq c) }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
