/-
`Main`'s callees linked (K4 of `notes/k8s-compactor-plan.md`), by hand as `compactwatch`'s
`MainLinked.lean`: `k8s_compactor.Main.wp_proof` applied to the linked results of the examples'
shared start (`etcdstart`'s `Link.lean`), of Kubernetes' compactor (etcd3's `Link.lean`, whose
`NewCompactor` is linked under the named hypothesis of `clock.RealClock.After`, as in client-go's link),
of `context`, to `ready`, `writer`, `check` and `apiserver` over them, and to the trust-boundary axioms of
`zap.NewNop` and `strconv.Itoa`. `Results.lean` restates it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.ready
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.writer
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.apiserver
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.check
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Link
public import Proof.go_uber_org.zap.NewNop
public import Proof.strconv.Itoa
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
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]
variable (h_After : EtcdGrove.clock.RealClock.After.spec (GF := GF) (hG := hG))

theorem k8s_compactor.wp_ready : k8s_compactor.ready.spec (GF := GF) (hG := hG) :=
  k8s_compactor.ready.wp_proof context.wp_Background context.WithTimeoutBackground.wp_proof
    context.wp_ErrAny

theorem k8s_compactor.wp_writer : k8s_compactor.writer.spec (GF := GF) (hG := hG) :=
  k8s_compactor.writer.wp_proof context.wp_Background context.WithTimeoutBackground.wp_proof
    context.wp_ErrAny strconv.Itoa.wp_proof

theorem k8s_compactor.wp_check : k8s_compactor.check.spec (GF := GF) (hG := hG) :=
  k8s_compactor.check.wp_proof k8s.compactor.wp_CompactRevision k8s.compactor.wp_Stop
    strconv.ParseInt.wp_proof context.wp_Background context.WithTimeoutBackground.wp_proof
    context.wp_ErrAny

include h_After in
theorem k8s_compactor.wp_apiserver : k8s_compactor.apiserver.spec (GF := GF) (hG := hG) :=
  k8s_compactor.apiserver.wp_proof (k8s.wp_NewCompactor h_After)
    (k8s.wp_StartCompactorPerEndpoint h_After) k8s_compactor.wp_check

include h_After in
/-- **The compactor example's `Main` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/compactor/Main.lean`), under the semantic premises
of its callees' linked results (as `compactwatch`'s) and the named hypothesis of
`clock.RealClock.After` (`time.After(d)`: a channel some time is sent on). -/
theorem k8s_compactor.wp_Main [Float64ToInt64Semantics]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    k8s_compactor.Main.spec (GF := GF) (hG := hG) :=
  k8s_compactor.Main.wp_proof zap.NewNop.wp_proof etcdstart.wp_StartCompactingServer
    etcdstart.wp_Serve etcdstart.wp_NewClient context.wp_ErrAny
    k8s_compactor.wp_ready k8s_compactor.wp_writer (k8s_compactor.wp_apiserver h_After)

end results

end EtcdGrove
end Perennial
