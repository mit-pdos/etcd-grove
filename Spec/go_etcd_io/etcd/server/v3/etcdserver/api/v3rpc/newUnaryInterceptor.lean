/-
`v3rpc.newUnaryInterceptor` (`v3rpc/interceptor.go`; unit P3b). Lean-first (no Rocq
counterpart); the vocabulary is `Proof/google_golang_org/grpc/InvGrpc.lean` and
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvQuota.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvQuota
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.UnaryChain

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`newUnaryInterceptor(s)`** returns a transparent interceptor (`srvInterceptorOk`, for requests
the learner check can read, `learnerReqOk`), whose resource is a level-0 thread token (prove-ps2-cap,
2026-11-23; until then none): `api.IsCapabilityEnabled` borrows `enableMapMu`'s reader slot with it,
before the handler's call, which the token is then lent to. It answers an error without
calling the handler if the v3 RPC capability is off, if the member is a learner and the request
not one a learner serves, if the client's API version is not UTF-8, or if the client requires a
leader and there is none; otherwise it calls the handler. Premises: the server's member id, its
`lead` (`s.Leader()`), its cluster (`IsMemberExist`, `IsLearner`) with the local member in it
(`membership.localKept`); under the thread bound `IsCapabilityEnabled`'s pool needs. (2026-11-24) It is the closure of
the function's code over a variable holding `s` (`v3rpc.isUnaryIc`, `UnaryChain.lean`), which the
members' axiom reads to name etcd's chain. -/
abbrev v3rpc.newUnaryInterceptor.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 30)] (s c : Loc) (mid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvMemberIDAddr s ↦□ mid ∗ srvLeadInv s ∗ srvClusterAddr s ↦□ c ∗
      membership.isRaftCluster c ∗ membership.localKept c }}
    (App (Val (@! v3rpc.newUnaryInterceptor)) (Val #s))
  {{ (ic : GoFunc), RET #ic; srvInterceptorOk ic (levelTok 0) v3rpc.learnerReqOk ∗
      v3rpc.isUnaryIc ic s }}

end spec

end EtcdGrove
end Perennial
