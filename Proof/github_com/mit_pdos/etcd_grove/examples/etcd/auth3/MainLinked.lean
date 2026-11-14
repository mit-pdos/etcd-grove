/-
`Main`'s callees linked (the auth3 Scope's A1, 2026-11-14), by hand, as putget3's
(`putget3/MainLinked.lean`): `etcd_auth3.Main.wp_proof` applied to `zap.NewNop`'s axiom, `startMember`'s
proof over the server's linked `NewServer.specM true` (`server_new_auth_on`, at D22's named
hypothesis `authSchemaSrv`, as authkv's `authkv_startServer`), `net.Listen`, `RaftHandler` and
`Start`, and authkv's linked `Run` (`auth/Link.lean`). `Results.lean` restates it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiResults
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.startMember
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Link
public import Proof.go_uber_org.zap.NewNop

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
(`server_new_auth_on`, at D22's named hypothesis), the raft handler served, `Start.spec`. -/
theorem etcd_auth3.wp_startMember (hD22 : ⊢ authSchemaSrv (GF := GF)) :
    etcd_auth3.startMember.spec (GF := GF) (hG := hG) :=
  etcd_auth3.startMember.wp_proof etcdstart.features.wp_NewDefaultServerFeatureGate
    (server_new_auth_on hD22) etcdstart.net.wp_Listen EtcdServer.wp_RaftHandler server_Start

/-- **auth3's `Main` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/auth3/Main.lean`). -/
theorem etcd_auth3.wp_Main [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [EtcdGrove.ErrorStringLeaf] (hD22 : ⊢ authSchemaSrv (GF := GF)) :
    etcd_auth3.Main.spec (GF := GF) (hG := hG) :=
  etcd_auth3.Main.wp_proof zap.NewNop.wp_proof (etcd_auth3.wp_startMember hD22) etcd_auth.wp_Run
    mvcc.api.mvccApi_names_nonempty_law_holds

end results

end EtcdGrove
end Perennial
