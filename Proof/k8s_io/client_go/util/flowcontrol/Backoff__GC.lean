/-
Proof of `Spec/k8s_io/client_go/util/flowcontrol/Backoff__GC.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: `Lock` through the guard (`isRWMutexGuard`), the clock's `Now`, the range over
the entries (`hasExpired`, `delete`), `Unlock`.

Still to add as hypotheses (callees without a spec yet): `Backoff.hasExpired` (body), `RWMutex.Lock`/`Unlock` through the guard (Perennial's `wp_Lock_guard`), `Time.Sub`/`Before` (Perennial).
-/
module

public import Spec.k8s_io.client_go.util.flowcontrol.Backoff__GC

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

theorem flowcontrol.Backoff.GC.wp_proof :
    flowcontrol.Backoff.GC.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
