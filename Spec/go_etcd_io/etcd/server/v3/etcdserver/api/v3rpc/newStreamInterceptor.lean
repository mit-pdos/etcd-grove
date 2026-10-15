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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`newStreamInterceptor(s)`** starts the leader monitor (`monitorLeader`) and returns a
transparent stream interceptor (`srvStreamInterceptorOk`, no resource): it answers an error
without calling the handler if the v3 RPC capability is off, if the member is a learner and the
method is not `Maintenance/Snapshot`, or if the client's API version is not UTF-8; otherwise it
counts the call (`clientRequests`) and calls the handler on the same server end and context.
The require-leader branch (the stream wrapped in a `serverStreamWithCtx` with a cancellable
context, registered in the monitor's map) is excluded by the premise `runsNoRequireLeader`, a
premise about the deployment (no client calls `WithRequireLeader`; `InvStreamInterceptor.lean`).
Premises: `newUnaryInterceptor.spec`'s (the member id, `lead`, the cluster with the local member
kept), `monitorLeader.spec`'s (`GoAttach`'s slots, returned; the `stopping` channel; the two
configuration fields), and `runsNoRequireLeader`. -/
abbrev v3rpc.newStreamInterceptor.spec : Prop :=
  ∀ (s c ch : Loc) (mid tm et : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvMemberIDAddr s ↦□ mid ∗ srvLeadInv s ∗ srvClusterAddr s ↦□ c ∗
      membership.isRaftCluster c ∗ membership.localKept c ∗
      srvGoRes s ∗ srvLgReader s ∗ srvStoppingAddr s ↦□ ch ∗ stopChan ch ∗
      cfgTickMsAddr (srvCfgAddr s) ↦□ tm ∗ cfgElectionTicksAddr (srvCfgAddr s) ↦□ et ∗
      v3rpc.runsNoRequireLeader }}
    (App (Val (@! v3rpc.newStreamInterceptor)) (Val #s))
  {{ (ic : GoFunc), RET #ic;
      srvStreamInterceptorOk ic iprop(True) ∗ srvGoRes s ∗ srvLgReader s }}

end spec

end EtcdGrove
end Perennial
