/-
## `WarnOfFailedRequest(lg, now, reqStringer, respMsg, err)` (`util.go`, names-only)

**Users.** The uber-applier's `dispatch` (`apply/uber_applier.go:101`, on an error). Snippet: none.

**Proof sketch.** Trust boundary, as `WarnOfExpensiveRequest`: `isNil`, `proto.Size`, `lg.Warn`.

**Changes.** As `WarnOfExpensiveRequest` (second pass: `stringerAt`, given back). **Margin.** None.
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

/-- `WarnOfFailedRequest(...)` with a stringer and a sizeable response: returns. -/
def WarnOfFailedRequest.spec : Prop :=
  ∀ (lg : Loc) (now : time.Time) (req msg : GoInterface) (o : Option (DFrac × Proto.Content))
    (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Zap.isLogger lg ∗ EtcdServerPb.stringerAt req ∗ msgOpt msg o }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfFailedRequest)) (Val #lg)) (Val #now)) (Val #req)) (Val #msg)) (Val #err))
  {{ RET #(); EtcdServerPb.stringerAt req ∗ msgOpt msg o }}

end spec
end Txn
end EtcdGrove
end Perennial
