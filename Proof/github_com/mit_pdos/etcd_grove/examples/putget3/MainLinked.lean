/-
`Main`'s callees linked (D21 stage M5, 2026-10-19), by hand, as putget's (`putget/MainLinked.lean`):
`putget3.Main.wp_proof` applied to the examples' shared start's linked `StartMember`, `Serve` and
`NewClient` (`common/Link.lean`, since 2026-10-22, D33), `context`'s `Background` and the axiom of
`zap.NewNop`. `Results.lean` restates it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget3.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Link
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.putget3.Assumptions]

/-- **putget3's `Main` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/putget3/Main.lean`), under the semantic premises of
its callees' linked results (putget's). -/
theorem putget3.wp_Main [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [ErrorStringLeaf]
    [ErrorStringNotWriter] :
    putget3.Main.spec (GF := GF) (hG := hG) :=
  putget3.Main.wp_proof zap.NewNop.wp_proof common.wp_StartMember common.wp_Serve
    common.wp_NewClient context.wp_Background context.WithTimeoutBackground.wp_proof
    context.wp_ErrAny

end results

end EtcdGrove
end Perennial
