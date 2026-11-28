/-
`Main`'s callees linked (auth-lease S4, `notes/auth-lease-s4-draft.md`, 2026-11-19), by hand, as authN's
(`authN/MainLinked.lean`) and leaseexpiryN's: `etcd_authlease.Main.wp_proof` applied to `zap.NewNop`'s axiom,
`etcdstart.Members`, `StartMembersAuth` over `StartMemberAuth` (as authN's), authlease's
`run` (with `barrier`, `barriers`, `newUserClient`, `grantPut`, `reqCtx`, `refused`, `noAuth`, `absent`,
`foreign`) over authkv's linked `SetUp` (`auth/Link.lean`), the client's linked lease methods
(`client/v3/Link.lean`) and the per-member lessor law `lessor_keys_of_read` (`LessorFollows.lean`); the expiry
arm's open case by `revokeExpiredLeases`' linked result (`srvRevokeOpen_intro`, as leaseexpiryN's); the
transport's directory bound for up to `1000` members by `rafthttp.bootCfg_of_le` (putgetN's).
`Results.lean` restates it. Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.protobuf.proto.MarshalBootConfChange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiResults
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.run
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.barrier
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.barriers
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.newUserClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.grantPut
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.reqCtx
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.refused
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.noAuth
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.absent
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.foreign
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartMemberAuth
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartMembersAuth
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.go_etcd_io.etcd.client.v3.Link
public import Proof.go_etcd_io.etcd.client.v3.WithLease
public import Proof.go_etcd_io.etcd.client.v3.WithAttachedKeys
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LessorFollows

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]

/-- **authlease's `newUserClient`** (authN's copy), over `clientv3.New`. -/
theorem etcd_authlease.wp_newUserClient :
    etcd_authlease.newUserClient.spec (GF := GF) (hG := hG) :=
  etcd_authlease.newUserClient.wp_proof client.v3.clientv3.wp_New

/-- **authlease's `barrier`**: root's linearizable read at a member. -/
theorem etcd_authlease.wp_barrier :
    etcd_authlease.barrier.spec (GF := GF) (hG := hG) :=
  etcd_authlease.barrier.wp_proof etcd_authlease.wp_newUserClient context.wp_ErrAny
    etcd_auth.context.wp_WithTimeoutBackground

/-- **authlease's `barriers`**: the barrier at every member. -/
theorem etcd_authlease.wp_barriers :
    etcd_authlease.barriers.spec (GF := GF) (hG := hG) :=
  etcd_authlease.barriers.wp_proof etcd_authlease.wp_barrier

/-- **authlease's `reqCtx`**: a request context carrying a token. -/
theorem etcd_authlease.wp_reqCtx :
    etcd_authlease.reqCtx.spec (GF := GF) (hG := hG) :=
  etcd_authlease.reqCtx.wp_proof etcd_auth.context.wp_WithTimeoutBackgroundMd context.wp_ErrAny
    etcd_auth.metadata.wp_AppendToOutgoingContext

/-- **authlease's `grantPut`**: a grant and a put attached to it. -/
theorem etcd_authlease.wp_grantPut :
    etcd_authlease.grantPut.spec (GF := GF) (hG := hG) :=
  etcd_authlease.grantPut.wp_proof context.wp_ErrAny etcd_auth.context.wp_WithTimeoutBackgroundMd
    WithLease.wp_proof

/-- **authlease's `noAuth`**: every lease method refused for a client with no or an invalid token. -/
theorem etcd_authlease.wp_noAuth :
    etcd_authlease.noAuth.spec (GF := GF) (hG := hG) :=
  etcd_authlease.noAuth.wp_proof etcd_authlease.wp_reqCtx etcd_authlease.refused.wp_proof
    client.v3.lessor.wp_Grant client.v3.lessor.wp_Revoke client.v3.lessor.wp_TimeToLive
    client.v3.lessor.wp_Leases WithAttachedKeys.wp_proof

/-- **authlease's `absent`**: root finds a key absent. -/
theorem etcd_authlease.wp_absent :
    etcd_authlease.absent.spec (GF := GF) (hG := hG) :=
  etcd_authlease.absent.wp_proof context.wp_ErrAny etcd_auth.context.wp_WithTimeoutBackground

/-- **authlease's `foreign`**: the lease methods on another principal's lease refused. -/
theorem etcd_authlease.wp_foreign :
    etcd_authlease.foreign.spec (GF := GF) (hG := hG) :=
  etcd_authlease.foreign.wp_proof etcd_authlease.wp_reqCtx etcd_authlease.refused.wp_proof
    client.v3.lessor.wp_Revoke client.v3.lessor.wp_TimeToLive client.v3.lessor.wp_Leases
    WithAttachedKeys.wp_proof

/-- **authlease's `run`** (`run.lean`), over authkv's linked `SetUp` (`auth/Link.lean`) and the per-member
lessor law. -/
theorem etcd_authlease.wp_run :
    etcd_authlease.run.spec (GF := GF) (hG := hG) :=
  etcd_authlease.run.wp_proof etcdstart.wp_Serve etcdstart.wp_NewClient auth.authStore.wp_BcryptCost
    context.wp_ErrAny etcd_auth.wp_SetUp etcd_authlease.wp_newUserClient etcd_authlease.wp_barriers
    etcd_authlease.wp_grantPut etcd_authlease.wp_noAuth etcd_authlease.refused.wp_proof
    etcd_authlease.wp_absent etcd_authlease.wp_foreign etcd_auth.context.wp_WithTimeoutBackgroundMd
    WithLease.wp_proof client.v3.wp_OpPut mvcc.api.mvccApi_persistent_law_holds
    mvcc.api.mvccApi_mvccState_reachable_law_holds lessor_keys_of_read

/-- **authlease's `Main(k)` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/authlease/Main.lean`). -/
theorem etcd_authlease.wp_Main :
    etcd_authlease.Main.spec (GF := GF) (hG := hG) :=
  etcd_authlease.Main.wp_proof zap.NewNop.wp_proof etcdstart.wp_Members
    (etcdstart.StartMembersAuth.wp_proof (etcdstart.StartMemberAuth.wp_proof
      etcdstart.features.wp_NewDefaultServerFeatureGate server_new_auth_on etcdstart.net.wp_ListenHttp
      EtcdServer.wp_RaftHandler server_Start)) etcd_authlease.wp_run
    (srvRevokeOpen_intro EtcdServer.wp_revokeExpiredLeases)
    mvcc.api.mvccApi_names_nonempty_law_holds
    (fun dir ps h hl => rafthttp.bootCfg_of_le dir ps h (by unfold peersMax; omega)) _root_.Perennial.EtcdGrove.proto.MarshalBootConfChange.wp_proof

end results

end EtcdGrove
end Perennial
