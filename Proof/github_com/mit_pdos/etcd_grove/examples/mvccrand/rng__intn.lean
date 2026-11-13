/- Lean-first (no Rocq counterpart). The proof of `rng.intn`: `next`, then the remainder below a
positive `n`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__intn
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__next

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- The remainder below a positive `n`, signed. -/
theorem intn_bound (z n : w64) (hn : 0 < sint.Z n) :
    0 ≤ sint.Z (z % n) ∧ sint.Z (z % n) < sint.Z n := by
  have h0 : 0 < n.toNat := by
    have : sint.Z n ≤ uint.Z n := by word
    unfold uint.Z at this; omega
  have hlt := Nat.mod_lt z.toNat h0
  have hu : uint.Z (z % n) < uint.Z n := by
    unfold uint.Z; rw [BitVec.toNat_umod]; exact_mod_cast hlt
  constructor <;> word

theorem rng.intn.wp_proof (wp_next : rng.next.spec (GF := GF) (hG := hG)) :
    rng.intn.spec (GF := GF) (hG := hG) := by
  intro r g n hn
  wp_start as Hr
  wp_auto
  wp_apply wp_next r g $$ [$Hr] as %z Hr
  have hn0 : ¬ uint.Z n = 0 := by have := (intn_bound n n hn).2; word
  simp only [hn0, ↓reduceIte]
  wp_auto
  iapply HΦ
  iframe
  ipureintro
  exact intn_bound z n hn

end proof

end mvccrand
end EtcdGrove
end Perennial
