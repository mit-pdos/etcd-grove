/-
`Main`'s callees linked (the closed lease example, 2026-11-02; as putget's), by hand: `leasekv.Main.wp_proof` applied to their
linked results in the examples' shared start's `Link.lean` (`common`'s, over the server's, v3rpc's
and the client's, since 2026-10-22, D33), `context`'s, and to the trust-boundary axiom of
`zap.NewNop`, which no `Link.lean` links yet. `etc/gen-link.py` has no
mode combining several packages' Links (each mode links one package, with `@` callees of the
Links it imports under one namespace); a `--leasekv` mode is the follow-up if more of the example
is linked. `Results.lean` restates it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.leasekv.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Link
public import Proof.go_etcd_io.etcd.client.v3.Link
public import Proof.go_uber_org.zap.NewNop
public import Proof.github_com.mit_pdos.etcd_grove.examples.leasekv.holdToken
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.leasekv.Assumptions]

/-- **The adequacy example's `Main` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/leasekv/Main.lean`), under the semantic premises of
its callees' linked results: `int64(f)` of a `float64` (`Float64ToInt64Semantics`, the server's)
and the client's `dialWithBalancer` body (`DialWithBalancerBody`). -/
theorem leasekv.wp_Main [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    leasekv.Main.spec (GF := GF) (hG := hG) :=
  leasekv.Main.wp_proof zap.NewNop.wp_proof leasekv.holdToken.wp_proof common.wp_StartServer common.wp_Serve
    common.wp_NewClient context.wp_Background context.WithTimeoutBackground.wp_proof
    context.wp_ErrAny client.v3.lessor.wp_Leases client.v3.lessor.wp_TimeToLive

end results


end EtcdGrove
end Perennial
