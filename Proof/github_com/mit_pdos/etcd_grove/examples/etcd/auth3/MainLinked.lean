/-
`Main`'s callees linked (the auth3 Scope's A1, 2026-11-14), by hand, as putget3's
(`putget3/MainLinked.lean`): `etcd_auth3.Main.wp_proof` applied to `zap.NewNop`'s axiom, `startMember`'s
proof over the server's linked `NewServer.specM true` (`server_new_auth_on`, as authkv's
`authkv_startServer`), `net.Listen`, `RaftHandler` and
`Start`, and auth3's `run` (A2, 2026-11-14: `run.lean`, with `barrier` and `newUserClient`) over authkv's
linked `SetUp`, `Work` and checks (`auth/Link.lean`). `Results.lean` restates it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiResults
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.run
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.barrier
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.newUserClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.startMember
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Assumptions]

/-- **A member started with auth on** (`startMember.lean`): `NewServer.specM true`
(`server_new_auth_on`), the raft handler served, `Start.spec`. -/
theorem etcd_auth3.wp_startMember [_root_.Perennial.net.FieldAssumptions] :
    etcd_auth3.startMember.spec (GF := GF) (hG := hG) :=
  etcd_auth3.startMember.wp_proof etcdstart.features.wp_NewDefaultServerFeatureGate
    server_new_auth_on etcdstart.net.wp_Listen EtcdServer.wp_RaftHandler server_Start

/-- **auth3's `newUserClient`** (authkv's copy), over `clientv3.New`. -/
theorem etcd_auth3.wp_newUserClient [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_auth3.newUserClient.spec (GF := GF) (hG := hG) :=
  etcd_auth3.newUserClient.wp_proof client.v3.clientv3.wp_New

/-- **auth3's `barrier`**: root's linearizable read at a member (`barrier.lean`). -/
theorem etcd_auth3.wp_barrier [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_auth3.barrier.spec (GF := GF) (hG := hG) :=
  etcd_auth3.barrier.wp_proof etcd_auth3.wp_newUserClient context.wp_ErrAny
    etcd_auth.context.wp_WithTimeoutBackground etcd_auth.client_Get_on_law_holds
    client.authTokReg_of_law_holds

/-- **auth3's `run`**: authkv's run across the three members (`run.lean`), over authkv's linked
`SetUp`, `Work` and checks (`auth/Link.lean`). -/
theorem etcd_auth3.wp_run [_root_.Perennial.net.FieldAssumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_auth3.run.spec (GF := GF) (hG := hG) :=
  etcd_auth3.run.wp_proof etcdstart.wp_Serve etcdstart.wp_NewClient auth.authStore.wp_BcryptCost
    context.wp_ErrAny etcd_auth.wp_SetUp etcd_auth3.wp_newUserClient etcd_auth3.wp_barrier
    etcd_auth.wp_Work etcd_auth.wp_Principals etcd_auth.wp_CheckHistory etcd_auth.wp_LastIn
    etcd_auth.context.wp_WithTimeoutBackground etcdstart.wp_Collect
    client.v3.watcher.wp_Watch etcd_auth.v3.wp_WithPrefix etcd_auth.v3.wp_WithRev
    etcd_auth.v3.wp_WithRange etcd_auth.wp_Permitted mvcc.api.mvccApi_persistent_law_holds
    mvcc.api.mvccApi_mvccState_reachable_law_holds

/-- **auth3's `Main` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/auth3/Main.lean`). -/
theorem etcd_auth3.wp_Main [_root_.Perennial.net.FieldAssumptions] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [EtcdGrove.ErrorStringLeaf] :
    etcd_auth3.Main.spec (GF := GF) (hG := hG) :=
  etcd_auth3.Main.wp_proof zap.NewNop.wp_proof etcd_auth3.wp_startMember etcd_auth3.wp_run
    mvcc.api.mvccApi_names_nonempty_law_holds

end results

end EtcdGrove
end Perennial
