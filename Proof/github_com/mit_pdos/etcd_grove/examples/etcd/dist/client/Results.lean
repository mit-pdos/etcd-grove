/-
# `etcd/dist/client`: the lease workloads, linked (#50 F2/F7, 2026-11-26)

The three lease workloads' runs of `examples/etcd/dist/client` with every callee's proof plugged in, at the
interim lease axioms (`notes/etcd-dist-f7.md`; the lead's request of #50 03:48Z: linked boot lemmas in a
non-statement linking module, the root of `etc/tcb-collections/etcd-dist-lease.txt`, no new top-level statement;
named `Results.lean`, not `LeaseResults.lean`, because `etc/proof_roots.py` takes its roots from `Link`/`MainLinked`/
`Results`/`TopLevelRobustness` files only):
- `wp_RunLeaseRead` (a cluster at lease mode `none`): `leaseReadCheck` over `newClient`, `leaseList.spec`
  (`Client_LeaseLeases_dist`), `Client_LeaseTimeToLive_dist`;
- `wp_RunLeaseCatchup` (lease mode `mono`): `leaseGrant.specMono` (`Lease_Grant_dist`), `leaseList.specGranted`
  (`Lease_LeasesGranted_dist`);
- `wp_RunLeaseExpiry` (lease mode `revocable`): `leaseGrant.spec` (`Lease_GrantLive_dist`), `leaseList.specLive`
  (`Lease_LeasesLive_dist`), `gone`.
The client's `newClient` is over `etcdstart`'s linked `NewClients`, `Client.Close` its trust-boundary axiom, `context`'s and `time.Sleep`'s linked results.

The lease mode and the lessor names' facts these runs' specs take (`Γ.kv.lm`, distinct `Γ.ls`, every member's
`leaseMember`) are what the cluster's start at that mode gives (`server/ClusterStartD.lean`, `clusterStartDL`:
`c.γk.lm = lm`, `c.NamesInj`, every member's `lease.lessorSlot`); the orchestrator's dispatch to them
(`MainReady`'s `switch`) is not linked here.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunLeaseRead
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunLeaseCatchup
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunLeaseExpiry
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.leaseReadCheck
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.leaseGrant
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.leaseList
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.gone
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.listed
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ended
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseGrantDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseGrantLiveDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseLeasesGrantedDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseLeasesLiveDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientLeaseLeasesDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientLeaseTTLDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.go_etcd_io.etcd.client.v3.Client__Close
public import Proof.go_uber_org.zap.NewNop
public import Perennial.Proof.context.Link
public import Proof.context.Link
public import Proof.context.WithTimeoutBackground
public import Perennial.Proof.time.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net etcd_dist

section links
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem' : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `newClient`, linked (`etcdstart`'s `NewClients`, `zap.NewNop`'s axiom). -/
theorem wp_newClientDist : newClient.spec (GF := GF) (hG := hG) :=
  newClient.wp_proof zap.NewNop.wp_proof etcdstart.wp_NewClients

/-- **`RunLeaseRead`, linked** (lease mode `none`), at `Client_LeaseLeases_dist` and
`Client_LeaseTimeToLive_dist`. -/
theorem wp_RunLeaseRead : RunLeaseRead.spec (GF := GF) (hG := hG) :=
  RunLeaseRead.wp_proof
    (leaseReadCheck.wp_proof wp_newClientDist
      (leaseList.wp_proof context.wp_Background context.WithTimeoutBackground.wp_proof context.wp_ErrAny
        view.Client_LeaseLeases_dist.wp_proof)
      context.wp_Background context.WithTimeoutBackground.wp_proof context.wp_ErrAny
      view.Client_LeaseTimeToLive_dist.wp_proof Client.Close.wp_proof)
    checked.wp_proof ended.wp_proof

/-- **`RunLeaseCatchup`, linked** (lease mode `mono`), at `Lease_Grant_dist` and `Lease_LeasesGranted_dist`. -/
theorem wp_RunLeaseCatchup : RunLeaseCatchup.spec (GF := GF) (hG := hG) :=
  RunLeaseCatchup.wp_proof wp_newClientDist
    (leaseGrant.wp_proofMono context.wp_Background context.WithTimeoutBackground.wp_proof context.wp_ErrAny
      view.Lease_Grant_dist.wp_proof)
    (leaseList.wp_proofGranted context.wp_Background context.WithTimeoutBackground.wp_proof context.wp_ErrAny
      view.Lease_LeasesGranted_dist.wp_proof)
    listed.wp_proof checked.wp_proof ended.wp_proof time.wp_Sleep Client.Close.wp_proof

/-- **`RunLeaseExpiry`, linked** (lease mode `revocable`), at `Lease_GrantLive_dist` and
`Lease_LeasesLive_dist`. -/
theorem wp_RunLeaseExpiry : RunLeaseExpiry.spec (GF := GF) (hG := hG) :=
  have wpL : leaseList.specLive (GF := GF) (hG := hG) :=
    leaseList.wp_proofLive context.wp_Background context.WithTimeoutBackground.wp_proof context.wp_ErrAny
      view.Lease_LeasesLive_dist.wp_proof
  RunLeaseExpiry.wp_proof wp_newClientDist
    (leaseGrant.wp_proof context.wp_Background context.WithTimeoutBackground.wp_proof context.wp_ErrAny
      view.Lease_GrantLive_dist.wp_proof)
    wpL (gone.wp_proof wpL listed.wp_proof time.wp_Sleep)
    listed.wp_proof checked.wp_proof ended.wp_proof Client.Close.wp_proof

end links

end etcd_dist_client
end EtcdGrove
end Perennial

end
