/-
Proof of `Spec/k8s_io/client_go/util/flowcontrol/NewBackOff.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: `NewBackOffWithJitter(initial, max, 0)`, then `newBackoff(clock.RealClock{}, ...)`:
the struct allocated, its map empty, the lock's guard allocated over `backoffEntries`.

Still to add as hypotheses (callees without a spec yet): `NewBackOffWithJitter`, `newBackoff` (bodies; their specs are this package's internal ones), `rand.New`/`NewSource` (names only), the clock's `RealClock` methods (`isClock`).
-/
module

public import Spec.k8s_io.client_go.util.flowcontrol.NewBackOff

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode 

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [fc_sem : k8s_io.client_go.util.flowcontrol.Assumptions]

theorem flowcontrol.NewBackOff.wp_proof :
    flowcontrol.NewBackOff.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
