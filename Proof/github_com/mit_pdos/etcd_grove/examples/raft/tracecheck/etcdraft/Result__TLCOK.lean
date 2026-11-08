/-
Lean-first (no Rocq counterpart). Layer C's Probe, the easy proof (2026-11-08,
`notes/trace-validation-plan.md`, "Probe set"): `Result.TLCOK` against its spec.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Result__TLCOK

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem Result.TLCOK.wp_proof : Result.TLCOK.spec (GF := GF) (hG := hG) := by
  intro r res
  wp_start as %Hrel
  obtain ⟨Hok, Hbr, -⟩ := Hrel
  wp_auto
  unfold Result.tlcOK
  rw [← Hok]
  cases r.OK' <;> wp_auto
  · iapply HΦ; ipureintro; trivial
  · have Hb : decide (r.Branched' = W64 0) = (true && res.branched == 0) := by
      rw [← Hbr]
      by_cases h : r.Branched' = W64 0
      · rw [h]; rfl
      · simp only [h, decide_false, Bool.true_and]
        symm; simp only [beq_eq_false_iff_ne]; intro h'; apply h; word
    rw [← Hb]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
