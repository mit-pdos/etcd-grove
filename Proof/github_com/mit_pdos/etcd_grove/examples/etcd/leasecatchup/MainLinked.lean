/-
`Main`'s callees linked (the multi-member lease example, lease-mono3 step 1, 2026-11-06,
`notes/lease-mono3-plan.md`), by hand, as leasegrant's: the example's own proofs (`config`, `grant`,
`leases`, `listed`, `run`, `Main`) applied to the linked results of the three-member cluster's
`Link.lean` (`StartCluster`, `PeerStep`), the examples' shared start's (`NewClients`), the client's
(`lessor.Grant`, `lessor.Leases`), `context`'s, and to the trust-boundary axiom of `zap.NewNop`.
`etc/gen-link.py` has no mode combining several packages' Links (as leasegrant's `MainLinked.lean`
says). `Results.lean` restates it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.run
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.config
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.grant
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.leases
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.listed
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Link
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Assumptions]

theorem etcd_leasecatchup.wp_config : etcd_leasecatchup.config.spec (GF := GF) (hG := hG) :=
  etcd_leasecatchup.config.wp_proof

theorem etcd_leasecatchup.wp_grant : etcd_leasecatchup.grant.spec (GF := GF) (hG := hG) :=
  etcd_leasecatchup.grant.wp_proof context.wp_Background context.WithTimeoutBackground.wp_proof
    context.wp_ErrAny client.v3.lessor.wp_Grant

theorem etcd_leasecatchup.wp_leases : etcd_leasecatchup.leases.spec (GF := GF) (hG := hG) :=
  etcd_leasecatchup.leases.wp_proof context.wp_Background context.WithTimeoutBackground.wp_proof
    context.wp_ErrAny client.v3.lessor.wp_Leases

theorem etcd_leasecatchup.wp_listed : etcd_leasecatchup.listed.spec (GF := GF) (hG := hG) :=
  etcd_leasecatchup.listed.wp_proof

/-- **`run` does not panic** (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leasecatchup/run.lean`),
under the semantic premise of its callees' linked results: the client's `dialWithBalancer` body
(`DialWithBalancerBody`). -/
theorem etcd_leasecatchup.wp_run [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_leasecatchup.run.spec (GF := GF) (hG := hG) :=
  etcd_leasecatchup.run.wp_proof etcd_leasecatchup.wp_config cluster3.wp_StartCluster
    etcdstart.wp_NewClients etcd_leasecatchup.wp_grant etcd_leasecatchup.wp_leases
    etcd_leasecatchup.wp_listed cluster3.wp_PeerStep

/-- **The multi-member lease example's `Main` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leasecatchup/Main.lean`), under `run`'s
semantic premises. -/
theorem etcd_leasecatchup.wp_Main [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_leasecatchup.Main.spec (GF := GF) (hG := hG) :=
  etcd_leasecatchup.Main.wp_proof zap.NewNop.wp_proof etcd_leasecatchup.wp_run

end results

end EtcdGrove
end Perennial
