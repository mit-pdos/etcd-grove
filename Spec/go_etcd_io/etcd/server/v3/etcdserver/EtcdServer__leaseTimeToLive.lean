/-
## `(*EtcdServer).leaseTimeToLive(ctx, r)` (internal helper; untranslated, an assumed contract)

Users: `LeaseTimeToLive` (`v3_server.go:713`). The code: on the leader, `waitAppliedIndex`, the
lessor's `Lookup` (3c: a lease the member applied, granted at some point; its remaining TTL, granted
TTL, keys attached at the member's applied revision), `ErrLeaseNotFound`, `ErrLeaderChanged` if the
lessor was demoted meanwhile; else forwarded to the leader (`waitLeader`, `leasehttp.TimeToLiveHTTP`:
the leader's answer, 3c's boundary), `ErrTimeout`/`ErrCanceled` at the context's end. Changes: the
old repository's names-only contract (`lease-grpc.md`'s `raftLeaseRead`) restated: an answer W0's
`leaseTimeToLive` step allows at every later state. Margin: the TTLs.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- An answer of W0's `leaseTimeToLive` step at every state from the return on (a reply
message), `ErrLeaseNotFound`, or an unsettled error. `Ans res` is the persistent fact of the answer,
given to the caller (who fires its update at the return). -/
def EtcdServer.leaseTimeToLive.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (who : Principal) (r : Loc) (dq : DFrac)
    (id : Int) (keys : Bool) (σ₀ : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ Context.ctxOk ctx ∗ threadTok ∗ etcdLb γ σ₀ ∗
      ClientV3.reqOwn r dq (.leaseTimeToLive id keys) }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"leaseTimeToLive")) (Val #ctx)) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      ClientV3.reqOwn r dq (.leaseTimeToLive id keys) ∗
      ((∃ res, ⌜∀ σ, Reach σ₀ σ → Step who (.leaseTimeToLive id keys) σ σ res⌝ ∗
          srvReply ClientV3.ansReply res resp err) ∨
       ⌜resp = null ∧ srvIndef err⌝) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
