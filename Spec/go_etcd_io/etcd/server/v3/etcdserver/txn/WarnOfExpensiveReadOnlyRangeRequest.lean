/-
## `WarnOfExpensiveReadOnlyRangeRequest(lg, d, now, reqStringer, rangeResponse, err)` (`util.go`)

**Users.** `EtcdServer.Range`'s deferred warning (`v3_server.go:126`: the request as its stringer,
the reply or `nil`). Snippet: none (a log line).

**Proof sketch.** `time.Since` (Perennial); past the duration, `isNil`, `len(Kvs)`, `proto.Size` (2a,
over the reply's content: 3h's relation law, depth at most `3`), `warnOfExpensiveGenericRequest`.

**Changes.** The old spec's lent `P` and `sizeOk` replaced by the reply itself (`optOwn`), given back.
**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `WarnOfExpensiveReadOnlyRangeRequest(...)` with a nil reply or a range reply: returns, the
reply given back. -/
def WarnOfExpensiveReadOnlyRangeRequest.spec : Prop :=
  ∀ (lg : Loc) (d : time.Duration) (now : time.Time) (req : GoInterface) (resp : Loc) (dq : DFrac)
    (mo : Option RangeRespM) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Zap.isLogger lg ∗ stringerOk req ∗ optOwn rangeRespOwn resp dq mo }}
    (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfExpensiveReadOnlyRangeRequest)) (Val #lg)) (Val #d)) (Val #now)) (Val #req)) (Val #resp)) (Val #err))
  {{ RET #(); optOwn rangeRespOwn resp dq mo }}

end spec
end Txn
end EtcdGrove
end Perennial
