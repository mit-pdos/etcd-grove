/-
Proof of `Spec/github_com/jonboulle/clockwork/realClock__Now.lean` (clockwork v0.5.0). Lean-first.
-/
module

public import Spec.github_com.jonboulle.clockwork.realClock__Now
public import Perennial.Spec.time.Now

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.jonboulle.clockwork.Assumptions]

theorem clockwork.realClock.Now.wp_proof (wp_Now : time.Now.spec (GF := GF) (hG := hG)) :
    clockwork.realClock.Now.spec (GF := GF) (hG := hG) := by
  intro rc
  wp_start
  wp_auto
  wp_apply wp_Now as %t -
  wp_end

end proof

end EtcdGrove
end Perennial
