/-
`v3rpc.newStreamInterceptor` (`v3rpc/interceptor.go`; the watch slice's unit W-W, 2026-10-15).
Lean-first (no Rocq counterpart); the vocabulary is
`Proof/google_golang_org/grpc/InvGrpcStream.lean` (`srvStreamInterceptorOk`) and
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvStreamInterceptor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvStreamInterceptor
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

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

/-- **`newStreamInterceptor(s)`** starts the leader monitor (`monitorLeader`) and returns a stream
interceptor that weakens the context (`srvStreamInterceptorWOk`, no resource; k8s 7f-4 item 7): it
answers an error without calling the handler if the v3 RPC capability is off, if the member is a
learner and the method is not `Maintenance/Snapshot`, if the client's API version is not UTF-8, or
if the client requires a leader and there is none (`ErrGRPCNoLeader`); otherwise it counts the call
(`clientRequests`) and calls the handler on the same server end, or, when the client requires a
leader, on a `serverStreamWithCtx` whose context is a `cancellableContext` over
`WithCancel(ss.Context())` registered in the monitor's map (a weak context with the same incoming
metadata), removed and cancelled when the handler returns. Premises: `newUnaryInterceptor.spec`'s
(the member id, `lead`, the cluster with the local member kept), `monitorLeader.spec`'s
(`GoAttach`'s slots, returned; the `stopping` channel; the two configuration fields),
and `newCancellableContext.spec`'s bound on threads (`runsNoRequireLeader`, unused since item 7, deleted
at step 6). -/
abbrev v3rpc.newStreamInterceptor.spec : Prop :=
  ∀ (s c ch : Loc) (mid tm et : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvMemberIDAddr s ↦□ mid ∗ srvLeadInv s ∗ srvClusterAddr s ↦□ c ∗
      membership.isRaftCluster c ∗ membership.localKept c ∗
      srvGoRes s ∗ srvLgReader s ∗ srvStoppingAddr s ↦□ ch ∗ stopChan ch ∗
      cfgTickMsAddr (srvCfgAddr s) ↦□ tm ∗ cfgElectionTicksAddr (srvCfgAddr s) ↦□ et ∗
      ⌜threadBound GF ≤ 2 ^ 30⌝ }}
    (App (Val (@! v3rpc.newStreamInterceptor)) (Val #s))
  {{ (ic : GoFunc), RET #ic;
      srvStreamInterceptorWOk ic iprop(True) ∗ srvGoRes s ∗ srvLgReader s }}

end spec

end EtcdGrove
end Perennial
