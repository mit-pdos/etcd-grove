/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/leasekv/Main.lean` (the closed lease
example, 2026-11-02, `notes/lease-ex-plan.md`; as putget's). Lean-first (no Rocq counterpart).

The steps (Prove stage): `Main`'s premises in the shared start's form; the ghost state `NewServer`
takes (`common.alloc1`); `common.StartServer`; `common.Serve` with the ghost step
`common.kv_lease_served` (the lease reads registered at the address); `common.NewClient`; each
read's context with the request timeout (`client.wp_WithTimeout_bg`); `cli.Lease.Leases` (`Q`: the
IDs have no duplicate) and the double loop's check; `cli.Lease.TimeToLive(leaseID)` (`Q`: the reply's
ID is `7`) and its check. Every step's error ends `Main` (`return`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.leasekv.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.leasekv.holdToken
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.StartServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClient
public import Spec.go_etcd_io.etcd.client.v3.lessor__TimeToLive
public import Spec.go_etcd_io.etcd.client.v3.lessor__Leases
public import Perennial.Spec.context.Background
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.ServedLease
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasekv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.leasekv.Assumptions]

/-- See the file header. -/
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_holdToken : holdToken.spec (GF := GF) (hG := hG))
    (wp_StartServer : common.StartServer.spec (GF := GF) (hG := hG))
    (wp_Serve : common.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : common.NewClient.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Leases : lessor.Leases.spec (GF := GF) (hG := hG))
    (wp_TimeToLive : lessor.TimeToLive.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end leasekv
end EtcdGrove
end Perennial
