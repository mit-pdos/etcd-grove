/- Lean-first (no Rocq counterpart).

The proof of `Main`: `CounterClock()` gives a clock (its invariant at `counterClockN`, apart
from the driver's `lintestN`); `Check(clock, 4, 10, 0)` then answers `Ok` (no timeout), so the
panic branch is not taken.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Check
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.CounterClock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace counter

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine

/-- The namespace of `Main`'s clock's invariant. -/
abbrev counterClockN : Namespace := nroot.@"counterClock"

theorem lintestN_counterClockN : (↑lintestN : CoPset) ⊆ ⊤ \ ↑counterClockN :=
  mask_ndot_ne' nroot "lintest" "counterClock" (by decide)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions]

theorem Main.wp_proof
    (wp_CounterClock : lintest.CounterClock.spec (GF := GF) (hG := hG))
    (wp_Check : Check.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro Hbound
  wp_start as #Hcc
  wp_apply wp_CounterClock counterClockN Hbound as %f ⟨%clockVal, #Hclk, Ht0⟩
  wp_apply wp_Check clockVal (W64 0) ↑counterClockN f (W64 4) (W64 10) (W64 0)
    lintestN_counterClockN (by decide) (by decide) (by decide) (by decide) $$ [Ht0]
    as %r %Hr
  · iframe
    iframe #
  obtain rfl := Hr.2 (by decide)
  wp_auto
  iapply HΦ
  itrivial

end proof

end counter
end lintest
end EtcdGrove
end Perennial
