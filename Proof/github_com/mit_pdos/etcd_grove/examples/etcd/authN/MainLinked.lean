/-
`Main`'s callees linked (authN, `notes/authN-plan.md`, 2026-11-16), by hand, as auth3's
(`auth3/MainLinked.lean`) and putgetN's: `etcd_authN.Main.wp_proof` applied to `zap.NewNop`'s axiom,
`etcdstart.Members` (`etcdstart/Link.lean`), `etcdstart.StartMembersAuth` over `StartMemberAuth`'s proof
over the server's linked `NewServer.specM true` (`server_new_auth_on`, as auth3's
`startMember`), `net.Listen`, `RaftHandler` and `Start`, and authN's `run`
(with `barrier` and `newUserClient`) over authkv's linked `SetUp`, `Work` and checks (`auth/Link.lean`);
the transport's directory bound for up to `1000` members by `rafthttp.bootCfg_of_le` (putgetN's).
`Results.lean` restates it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiResults
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authN.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authN.run
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authN.barrier
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authN.newUserClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartMemberAuth
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartMembersAuth
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Link
public import Proof.go_uber_org.zap.NewNop
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.ClientOn
public import Proof.go_etcd_io.etcd.client.v3.AuthnServedOn

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authN.Assumptions]

/-- **A member started with auth on, at any token and snapshot settings** (`StartMemberAuth.lean`):
`NewServer.specM true` (`server_new_auth_on`), the raft handler served,
`Start.spec`. -/
theorem etcd_authN.wp_StartMemberAuth [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] :
    etcdstart.StartMemberAuth.spec (GF := GF) (hG := hG) :=
  etcdstart.StartMemberAuth.wp_proof etcdstart.features.wp_NewDefaultServerFeatureGate
    server_new_auth_on etcdstart.net.wp_Listen EtcdServer.wp_RaftHandler server_Start

/-- **The `k` members started with auth on** (`StartMembersAuth.lean`). -/
theorem etcd_authN.wp_StartMembersAuth [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] :
    etcdstart.StartMembersAuth.spec (GF := GF) (hG := hG) :=
  etcdstart.StartMembersAuth.wp_proof etcd_authN.wp_StartMemberAuth

/-- **authN's `newUserClient`** (auth3's copy), over `clientv3.New`. -/
theorem etcd_authN.wp_newUserClient [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_authN.newUserClient.spec (GF := GF) (hG := hG) :=
  etcd_authN.newUserClient.wp_proof client.v3.clientv3.wp_New

/-- **authN's `barrier`**: root's linearizable read at a member (`barrier.lean`). -/
theorem etcd_authN.wp_barrier [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_authN.barrier.spec (GF := GF) (hG := hG) :=
  etcd_authN.barrier.wp_proof etcd_authN.wp_newUserClient context.wp_ErrAny
    etcd_auth.context.wp_WithTimeoutBackground etcd_auth.client_Get_on_law_holds
    client.authTokReg_of_law_holds

/-- **authN's `run`**: authkv's run across the `k` members (`run.lean`), over authkv's linked
`SetUp`, `Work` and checks (`auth/Link.lean`). -/
theorem etcd_authN.wp_run [_root_.Perennial.net.FieldAssumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_authN.run.spec (GF := GF) (hG := hG) :=
  etcd_authN.run.wp_proof etcdstart.wp_Serve etcdstart.wp_NewClient auth.authStore.wp_BcryptCost
    context.wp_ErrAny etcd_auth.wp_SetUp etcd_authN.wp_newUserClient etcd_authN.wp_barrier
    etcd_auth.wp_Work etcd_auth.wp_Principals etcd_auth.wp_CheckHistory etcd_auth.wp_LastIn
    etcd_auth.context.wp_WithTimeoutBackground etcdstart.wp_Collect
    client.v3.watcher.wp_Watch etcd_auth.v3.wp_WithPrefix etcd_auth.v3.wp_WithRev
    etcd_auth.v3.wp_WithRange etcd_auth.wp_Permitted mvcc.api.mvccApi_persistent_law_holds
    mvcc.api.mvccApi_mvccState_reachable_law_holds

/-- **authN's `Main(k)` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/authN/Main.lean`). -/
theorem etcd_authN.wp_Main [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_authN.Main.spec (GF := GF) (hG := hG) :=
  etcd_authN.Main.wp_proof zap.NewNop.wp_proof etcdstart.wp_Members
    etcd_authN.wp_StartMembersAuth etcd_authN.wp_run
    mvcc.api.mvccApi_names_nonempty_law_holds
    (fun dir ps h hl => rafthttp.bootCfg_of_le dir ps h (by unfold peersMax; omega))

end results

end EtcdGrove
end Perennial
