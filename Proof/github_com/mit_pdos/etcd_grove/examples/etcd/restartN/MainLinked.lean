/-
**restartN's `Main(k)`, linked** (`notes/restartN-plan.md`, 2026-11-15): its proof over the linked results
of its callees: etcdstart's `Members` and `BuildServer` (and its restart), the server's `Start`,
`RaftHandler`, `Put`, `Range`, `Leader`, `MemberID`, `HardStop`, `AppliedIndex`, `net.Listen`,
`sync.Mutex`'s `Lock`/`Unlock`, `context`'s, `zap.NewNop`; its own start loop (`startMembers`, which mirrors
`etcdstart.StartMembers`' steps but serves each member's peer address through the member's `raftSwap`
instead of its raft handler directly) and `raftSwap` handler (`ServeHTTP`, `set`); mvcc's two laws; and
`rafthttp.bootCfg_of_le` (a directory of up to `1000` members is within the transport's `peersMax`, as for
putgetN). Lean-first (no Rocq counterpart); restart3's `MainLinked.lean` with putgetN's start.
-/
module

public import Proof.google_golang_org.protobuf.proto.MarshalBootConfChange
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Run
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.startMembers
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.build
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.newMember
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.raftSwap
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.put
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.stop
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.check
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.go_uber_org.zap.NewNop
public import Perennial.Proof.context.Link
public import Perennial.Proof.sync.Link
public import Proof.context.Link
public import Proof.context.WithTimeoutBackground
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiResults

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]

/-- **restartN's `Main(k)` does not panic** (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restartN/Main.lean`),
over its callees' linked results. -/
theorem etcd_restartN.wp_Main [go_etcd_io.etcd.cache.v3.Assumptions] :
    etcd_restartN.Main.spec (GF := GF) (hG := hG) :=
  etcd_restartN.Main.wp_proof zap.NewNop.wp_proof
    (etcd_restartN.Run.wp_proof etcdstart.wp_Members
      (etcd_restartN.startMembers.wp_proof
        (etcd_restartN.build.wp_proof etcdstart.wp_BuildServerF)
        (etcd_restartN.newMember.wp_proof etcdstart.net.wp_ListenHttp EtcdServer.wp_RaftHandler
          EtcdServer.wp_Start
          (etcd_restartN.raftSwap.ServeHTTP.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock)))
      (etcd_restartN.put.wp_proof EtcdServer.wp_Put context.wp_Background
        context.WithTimeoutBackground.wp_proof)
      EtcdServer.wp_Leader EtcdServer.wp_MemberID
      (etcd_restartN.stop.wp_proof EtcdServer.wp_AppliedIndex EtcdServer.wp_HardStop)
      (etcd_restartN.restartMember.wp_proof
        (etcd_restartN.build.wp_proofRestart etcdstart.wp_BuildServerRestart)
        EtcdServer.wp_RaftHandler
        (etcd_restartN.raftSwap.set.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock)
        EtcdServer.wp_Start)
      (etcd_restartN.check.wp_proof EtcdServer.wp_Range EtcdServer.wp_Leader context.wp_Background
        context.WithTimeoutBackground.wp_proof)
      mvcc.api.mvccApi_names_nonempty_law_holds mvcc.api.mvccApi_mvccReaders_split_law_holds
      (fun dir ps h hl => rafthttp.bootCfg_of_le dir ps h (by unfold peersMax; omega)) _root_.Perennial.EtcdGrove.proto.MarshalBootConfChange.wp_proof)

end results

end EtcdGrove
end Perennial
