/-
## `WarnOfExpensiveRequest(lg, d, now, reqStringer, respMsg, err)` (`util.go`, names-only)

**Users.** The uber-applier's `dispatch` (`apply/uber_applier.go:99`: a `*pb.InternalRaftStringer`
of the entry's request, the apply's response or `nil`). Snippet: none (a log line).

**Proof sketch.** Trust boundary: the function is names-only in the translation
(`Code/.../txn.toml`); true of `util.go`: `time.Since`, and past the duration `isNil`,
`proto.Size` (a message within protobuf's depth: `msgOpt`), `warnOfExpensiveGenericRequest`
(`lg.Warn`, the stringer's `String()`).

**Changes.** The old spec's premise (a fresh `InternalRaftStringer` of a non-nil request) as
3h's `EtcdServerPb.stringerAt` (given back; second pass: was the provisional persistent
`stringerOk`), and the response sized (`msgOpt`, given back).
**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

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

/-- `WarnOfExpensiveRequest(...)` with a stringer and a sizeable response: returns. -/
def WarnOfExpensiveRequest.spec : Prop :=
  ∀ (lg : Loc) (d : time.Duration) (now : time.Time) (req msg : GoInterface)
    (o : Option (DFrac × Proto.Content)) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Zap.isLogger lg ∗ EtcdServerPb.stringerAt req ∗ msgOpt msg o }}
    (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfExpensiveRequest)) (Val #lg)) (Val #d)) (Val #now)) (Val #req)) (Val #msg)) (Val #err))
  {{ RET #(); EtcdServerPb.stringerAt req ∗ msgOpt msg o }}

end spec
end Txn
end EtcdGrove
end Perennial
