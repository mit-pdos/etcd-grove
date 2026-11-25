/-
**restart1's `Main`, linked** (restart S7.5, 2026-11-14): its proof over the linked results of its
callees (etcdstart's `BuildServer` and its restart, the server's `Start`, `Put`, `Range`, `Leader`,
`HardStop`, `AppliedIndex`, `context`'s, `zap.NewNop`) and mvcc's two laws. Lean-first (no Rocq
counterpart); putget's `MainLinked.lean`.
-/
module

public import Proof.google_golang_org.protobuf.proto.MarshalBootConfChange
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Run
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.startMember
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.put
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.stop
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.check
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.go_uber_org.zap.NewNop
public import Perennial.Proof.context.Link
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Assumptions]

/-- **restart1's `Main` does not panic** (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restart1/Main.lean`),
over its callees' linked results. -/
theorem etcd_restart1.wp_Main
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] [go_etcd_io.etcd.cache.v3.Assumptions] :
    etcd_restart1.Main.spec (GF := GF) (hG := hG) :=
  etcd_restart1.Main.wp_proof zap.NewNop.wp_proof
    (etcd_restart1.Run.wp_proof
      (etcd_restart1.startMember.wp_proof etcdstart.wp_BuildServer EtcdServer.wp_Start)
      (etcd_restart1.startMember.wp_proofRestart etcdstart.wp_BuildServerRestart EtcdServer.wp_Start)
      (etcd_restart1.put.wp_proof EtcdServer.wp_Put context.wp_Background
        context.WithTimeoutBackground.wp_proof)
      (etcd_restart1.stop.wp_proof EtcdServer.wp_AppliedIndex EtcdServer.wp_HardStop)
      (etcd_restart1.check.wp_proof EtcdServer.wp_Range EtcdServer.wp_Leader context.wp_Background
        context.WithTimeoutBackground.wp_proof)
      mvcc.api.mvccApi_names_nonempty_law_holds mvcc.api.mvccApi_mvccReaders_split_law_holds _root_.Perennial.EtcdGrove.proto.MarshalBootConfChange.wp_proof)

end results

end EtcdGrove
end Perennial
