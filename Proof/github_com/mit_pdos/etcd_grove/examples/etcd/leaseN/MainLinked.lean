/-
**leaseN's `Main(k)`, linked** (`notes/leaseN-plan.md`, 2026-11-16): `Main.wp_proof` with its callees'
linked results (putgetN's start, `etcdstart.Serve`, the client's `NewClient`, `Leases`, `TimeToLive`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.protobuf.proto.MarshalBootConfChange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiResults
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.run
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.check
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.go_etcd_io.etcd.client.v3.Link
public import Proof.go_uber_org.zap.NewNop
public import Perennial.Proof.context.Link
public import Proof.context.Link
public import Proof.context.WithTimeoutBackground

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Assumptions]

/-- **leaseN's `check` does not panic** (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseN/check.lean`). -/
theorem etcd_leaseN.wp_check :
    etcd_leaseN.check.spec (GF := GF) (hG := hG) :=
  etcd_leaseN.check.wp_proof etcdstart.wp_NewClient context.wp_Background
    context.WithTimeoutBackground.wp_proof context.wp_ErrAny client.v3.lessor.wp_TimeToLive
    client.v3.lessor.wp_Leases

/-- **leaseN's `run` does not panic** (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseN/run.lean`). -/
theorem etcd_leaseN.wp_run :
    etcd_leaseN.run.spec (GF := GF) (hG := hG) :=
  etcd_leaseN.run.wp_proof etcdstart.wp_Serve etcd_leaseN.wp_check

/-- **leaseN's `Main(k)` does not panic** (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseN/Main.lean`),
under the semantic premises of its callees' linked results (putgetN's). -/
theorem etcd_leaseN.wp_Main :
    etcd_leaseN.Main.spec (GF := GF) (hG := hG) :=
  etcd_leaseN.Main.wp_proof zap.NewNop.wp_proof etcdstart.wp_Members etcdstart.wp_StartMembers
    etcd_leaseN.wp_run mvcc.api.mvccApi_names_nonempty_law_holds
    (fun dir ps h hl => rafthttp.bootCfg_of_le dir ps h (by unfold peersMax; omega)) _root_.Perennial.EtcdGrove.proto.MarshalBootConfChange.wp_proof

end results

end EtcdGrove
end Perennial
