/-
**restart3's `Main`, linked** (restart3 C4, 2026-11-15): its proof over the linked results of its
callees (etcdstart's `BuildServer` and its restart, the server's `Start`, `RaftHandler`, `Put`, `Range`,
`Leader`, `MemberID`, `HardStop`, `AppliedIndex`, `net.Listen`, `sync.Mutex`'s `Lock`/`Unlock`,
`context`'s, `zap.NewNop`), its own `raftSwap` handler (`ServeHTTP`, `set`) and mvcc's two laws.
Lean-first (no Rocq counterpart); restart1's `MainLinked.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.Run
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.build
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.newMember
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.raftSwap
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.put
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.stop
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.check
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]

/-- **restart3's `Main` does not panic** (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restart/Main.lean`),
over its callees' linked results. -/
theorem etcd_restart.wp_Main [_root_.Perennial.net.FieldAssumptions] [go_etcd_io.etcd.cache.v3.Assumptions] :
    etcd_restart.Main.spec (GF := GF) (hG := hG) :=
  etcd_restart.Main.wp_proof zap.NewNop.wp_proof
    (etcd_restart.Run.wp_proof
      (etcd_restart.build.wp_proof etcdstart.wp_BuildServer)
      (etcd_restart.newMember.wp_proof etcdstart.net.wp_ListenHttp EtcdServer.wp_RaftHandler
        EtcdServer.wp_Start
        (etcd_restart.raftSwap.ServeHTTP.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock))
      (etcd_restart.put.wp_proof EtcdServer.wp_Put context.wp_Background
        context.WithTimeoutBackground.wp_proof)
      EtcdServer.wp_Leader EtcdServer.wp_MemberID
      (etcd_restart.stop.wp_proof EtcdServer.wp_AppliedIndex EtcdServer.wp_HardStop)
      (etcd_restart.restartMember.wp_proof
        (etcd_restart.build.wp_proofRestart etcdstart.wp_BuildServerRestart)
        EtcdServer.wp_RaftHandler
        (etcd_restart.raftSwap.set.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock)
        EtcdServer.wp_Start)
      (etcd_restart.check.wp_proof EtcdServer.wp_Range EtcdServer.wp_Leader context.wp_Background
        context.WithTimeoutBackground.wp_proof)
      mvcc.api.mvccApi_names_nonempty_law_holds mvcc.api.mvccApi_mvccReaders_split_law_holds)

end results

end EtcdGrove
end Perennial
