/- Lean-first (no Rocq counterpart). Small lemmas the stream leaves' proofs share
(`stream.expect`): a watcher's position fields out of its struct's points-to, and back. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.watcher__matches

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

/-! ### `pick`'s weights (`pick.specW`) -/

/-- The sum of the positive weights among the first `k` of `zs`. -/
def psum (zs : List Int) (k : Nat) : Int := ((zs.take k).map (fun z => max 0 z)).sum

theorem psum_zero (zs : List Int) : psum zs 0 = 0 := by simp [psum]

theorem psum_succ (zs : List Int) (k : Nat) :
    psum zs (k + 1) = psum zs k + max 0 (zs.getD k 0) := by
  unfold psum
  rw [List.take_add_one, List.map_append, List.sum_append]
  cases h : zs[k]? with
  | none => simp [List.getD, h]
  | some z => simp [List.getD, h]

theorem psum_nonneg (zs : List Int) (k : Nat) : 0 ≤ psum zs k := by
  induction k with
  | zero => simp [psum_zero]
  | succ k ih => rw [psum_succ]; omega

theorem psum_mono (zs : List Int) {k k' : Nat} (h : k ≤ k') : psum zs k ≤ psum zs k' := by
  induction k' with
  | zero => rw [Nat.le_zero.1 h]; exact Int.le_refl _
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with h1 | h1
    · have := ih (by omega); rw [psum_succ]; omega
    · rw [show k = k' + 1 by omega]; exact Int.le_refl _

theorem psum_ge (zs : List Int) {j k : Nat} (h : j < k) : max 0 (zs.getD j 0) ≤ psum zs k := by
  have h1 := psum_mono zs (show j + 1 ≤ k by omega)
  rw [psum_succ] at h1
  have := psum_nonneg zs j
  omega

theorem psum_len (zs : List Int) {k : Nat} (h : zs.length ≤ k) : psum zs k = psum zs zs.length := by
  unfold psum; rw [List.take_of_length_le h, List.take_length]

/-- A loop over `[0, min(m, |zs|))` ends at `k`: its sum is the first `m`'s. -/
theorem psum_exit (zs : List Int) {k m : Nat} (hk : k ≤ zs.length) (hm : k ≤ m)
    (hexit : m ≤ k ∨ zs.length ≤ k) : psum zs m = psum zs k := by
  rcases hexit with h | h
  · rw [show m = k by omega]
  · rw [psum_len zs (show zs.length ≤ m by omega), psum_len zs h]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- **A watcher's position fields** (`rev`, `index`) out of its struct, and the struct back. -/
theorem watcher_pos_split (w : Loc) (wv : watcher) (dq : DFrac) :
    (w ↦{dq} wv : IProp GF) ⊢ w.[watcher, go!"rev"] ↦{dq} wv.rev' ∗ w.[watcher, go!"index"] ↦{dq} wv.index' ∗
      (w.[watcher, go!"rev"] ↦{dq} wv.rev' -∗ w.[watcher, go!"index"] ↦{dq} wv.index' -∗
        w ↦{dq} wv) := by
  iintro Hw
  icases (typedPointsto_not_null_dup _ _ _) $$ Hw with ⟨Hw, %Hwn⟩
  iStructNamedSuffix Hw "W"
  iframe revW indexW
  iintro revW indexW
  iapply typedPointsto_combine w _ dq Hwn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
