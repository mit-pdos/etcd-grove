/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/leasegrant/Main.lean` (the closed
lease-grant example, 2026-11-02, `notes/lease-grant-plan.md`; as leasekv's). Lean-first (no Rocq
counterpart). Not proved (Draft).

The steps (Prove stage): `Main`'s premises in the shared start's form; the ghost state `NewServer`
takes, at KV names that grant leases (`KVNames.lg = true`: a variant of `common.alloc1`);
`common.StartServer`; `go holdToken()` (`wp_fork_tok_self`); `common.Serve` with the ghost step
`common.kv_lease_grant_served` (the lease reads and grants registered at the address);
`common.NewClient`; each call's context with the request timeout (`client.wp_WithTimeout_bg`);
`cli.Lease.Grant(600)` (at `etcdLeaseGrantSpecL`: `Q` keeps the reply's lease granted at an index
of the lessor's history, `leaseGrantedAt`); `cli.Lease.Leases()` (at `etcdLeaseLeasesSpecL`, handing
in `[g.ID]` with its grant: `Q`, the reply lists it) and the loop's check. Every step's error ends
`Main` (`return`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.leasegrant.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.leasegrant.holdToken
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.StartServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClient
public import Spec.go_etcd_io.etcd.client.v3.lessor__Grant
public import Spec.go_etcd_io.etcd.client.v3.lessor__Leases
public import Perennial.Spec.context.Background
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.ServedLeaseGrant
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasegrant

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.leasegrant.Assumptions]

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
    (wp_Grant : lessor.Grant.spec (GF := GF) (hG := hG))
    (wp_Leases : lessor.Leases.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end leasegrant
end EtcdGrove
end Perennial
