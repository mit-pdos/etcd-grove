/- Lean-first (no Rocq counterpart). The proof of `compOk`. -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.compOk

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem compOk.wp_proof : compOk.spec (GF := GF) (hG := hG) := by
  intro n dots
  wp_start
  try wp_auto
  wp_if_destruct
  · rw [show tCompOk (uint.nat (W64 0)) dots = false by simp [tCompOk]]
    iapply HΦ; itrivial
  · have h0 : uint.nat n ≠ 0 := by intro h; apply Hif; word
    try wp_auto
    wp_if_destruct
    · have h1 : uint.nat n ≤ 255 := by word
      have h2 : (uint.nat n ≤ 2) ↔ uint.Z n ≤ uint.Z (W64 2) := by constructor <;> intro <;> word
      try wp_auto
      wp_if_destruct
      all_goals first
        | (rw [show tCompOk (uint.nat n) true = !decide (uint.Z n ≤ uint.Z (W64 2)) by
              unfold tCompOk
              rw [show decide (uint.nat n ≤ 2) = decide (uint.Z n ≤ uint.Z (W64 2)) from
                decide_eq_decide.mpr h2]
              simp [h0, h1]]
           iapply HΦ; itrivial)
        | (rw [show tCompOk (uint.nat n) false = true by unfold tCompOk; simp [h0, h1]]
           iapply HΦ; itrivial)
    · have h1 : ¬ uint.nat n ≤ 255 := by word
      rw [show tCompOk (uint.nat n) dots = false by unfold tCompOk; simp [h1]]
      iapply HΦ; itrivial

end proof

end etcd_wal
end EtcdGrove
end Perennial
