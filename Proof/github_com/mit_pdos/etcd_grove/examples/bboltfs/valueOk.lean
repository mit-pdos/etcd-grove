/- Lean-first (no Rocq counterpart). The proof of `valueOk`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.valueOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

theorem valueOk.wp_proof : valueOk.spec (GF := GF) (hG := hG) := by
  intro txid v has
  wp_start
  wp_auto
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    ipureintro
    have h1 : txid.toNat ≤ 1 := by
      have : uint.Z txid ≤ uint.Z (W64 1) := by simpa using Hif
      have h' : uint.Z (W64 1) = 1 := rfl
      simp only [uint.Z] at this h'; omega
    simp only [valueOkP, if_pos h1]
    cases has <;> simp
  · have h1 : ¬ txid.toNat ≤ 1 := by
      have : ¬ uint.Z txid ≤ uint.Z (W64 1) := by simpa using Hif
      have h' : uint.Z (W64 1) = 1 := rfl
      simp only [uint.Z] at this h'; omega
    have hw : W64 (txid.toNat : Int) = txid := by
      apply BitVec.eq_of_toNat_eq; simp
    cases has
    · (try wp_auto)
      iapply HΦ
      ipureintro
      simp [valueOkP, if_neg h1]
    · (try wp_auto)
      iapply HΦ
      ipureintro
      simp only [valueOkP, if_neg h1, hw, if_pos, decide_eq_true_iff, Option.some.injEq]

end proof

end bboltfs
end EtcdGrove
end Perennial
