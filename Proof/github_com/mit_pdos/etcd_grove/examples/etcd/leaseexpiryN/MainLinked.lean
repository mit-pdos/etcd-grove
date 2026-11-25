/-
**leaseexpiryN's `Main(k)`, linked** (`notes/leaseN-plan.md`, 2026-11-16): `Main.wp_proof` with its callees'
linked results (putgetN's start, `etcdstart.Serve`, the client's `NewClient`, `Grant`, `Leases`; `revokeExpiredLeases`' linked
result for the expiry arm's open case, `srvRevokeOpen_intro`, as `etcd_leaseexpiry`'s).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.protobuf.proto.MarshalBootConfChange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiResults
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.run
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.grant
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.leases
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.listed
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.gone
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Assumptions]

/-- **leaseexpiryN's `grant`** (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiryN/grant.lean`). -/
theorem etcd_leaseexpiryN.wp_grant :
    etcd_leaseexpiryN.grant.spec (GF := GF) (hG := hG) :=
  etcd_leaseexpiryN.grant.wp_proof context.wp_Background context.WithTimeoutBackground.wp_proof
    context.wp_ErrAny client.v3.lessor.wp_Grant

/-- **leaseexpiryN's `leases`** (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiryN/leases.lean`). -/
theorem etcd_leaseexpiryN.wp_leases :
    etcd_leaseexpiryN.leases.spec (GF := GF) (hG := hG) :=
  etcd_leaseexpiryN.leases.wp_proof context.wp_Background context.WithTimeoutBackground.wp_proof
    context.wp_ErrAny client.v3.lessor.wp_Leases

/-- **leaseexpiryN's `gone`** (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiryN/gone.lean`). -/
theorem etcd_leaseexpiryN.wp_gone :
    etcd_leaseexpiryN.gone.spec (GF := GF) (hG := hG) :=
  etcd_leaseexpiryN.gone.wp_proof etcd_leaseexpiryN.wp_leases etcd_leaseexpiryN.listed.wp_proof
    time.wp_Sleep

/-- **leaseexpiryN's `run` does not panic** (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiryN/run.lean`). -/
theorem etcd_leaseexpiryN.wp_run [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_leaseexpiryN.run.spec (GF := GF) (hG := hG) :=
  etcd_leaseexpiryN.run.wp_proof etcdstart.wp_Serve etcdstart.wp_NewClient etcd_leaseexpiryN.wp_grant
    etcd_leaseexpiryN.wp_leases etcd_leaseexpiryN.listed.wp_proof etcd_leaseexpiryN.wp_gone

/-- **leaseexpiryN's `Main(k)` does not panic** (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiryN/Main.lean`),
under the semantic premises of its callees' linked results (putgetN's). -/
theorem etcd_leaseexpiryN.wp_Main [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_leaseexpiryN.Main.spec (GF := GF) (hG := hG) :=
  etcd_leaseexpiryN.Main.wp_proof zap.NewNop.wp_proof etcdstart.wp_Members etcdstart.wp_StartMembers
    etcd_leaseexpiryN.wp_run (srvRevokeOpen_intro EtcdServer.wp_revokeExpiredLeases)
    mvcc.api.mvccApi_names_nonempty_law_holds
    (fun dir ps h hl => rafthttp.bootCfg_of_le dir ps h (by unfold peersMax; omega)) _root_.Perennial.EtcdGrove.proto.MarshalBootConfChange.wp_proof

end results

end EtcdGrove
end Perennial
