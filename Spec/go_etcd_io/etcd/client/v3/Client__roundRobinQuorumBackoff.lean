/-
`c.roundRobinQuorumBackoff(waitBetween, jitterFraction, backoffExponent, maxWaitBetween)`
(`client/v3/client.go`; changed by PR etcd#20731, which adds the last two parameters and computes
the wait with `expBackoff`): the backoff function `dialSetupOpts` installs in the retry
interceptor (`withBackoff`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (backoffOk)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- On a client `clientv3.New` built (`retryClientOk`: its logger), `roundRobinQuorumBackoff`
returns a backoff function that returns on every attempt (`backoffOk`, what the retry
interceptor's options require of `backoffFunc`): in particular it never divides by zero (the
quorum `len(endpoints)/2 + 1` is never 0, nor wraps). The same spec holds of the code before the
PR; the wait's value is outside it (float arithmetic: `expBackoff.spec`, `jitterUp.spec`). -/
abbrev Client.roundRobinQuorumBackoff.spec : Prop :=
  ∀ (c : Loc) (wb jf ex mw : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c }}
    (App (App (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
      go!"roundRobinQuorumBackoff")) (Val #wb)) (Val #jf)) (Val #ex)) (Val #mw))
  {{ (bf : GoFunc), RET #bf; backoffOk bf }}

end spec

end EtcdGrove
end Perennial
