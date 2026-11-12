/-
`UnsafeByteSlice`'s proof (`internal/common/unsafe.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.UnsafeByteSlice
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import Perennial.Golang.Theory.Plain

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem UnsafeByteSlice.wp_proof : UnsafeByteSlice.spec (GF := GF) (hG := hG) := by
  intro base off i j H1 H2 H3 H4
  wp_start
  wp_auto
  wp_func_call
  wp_call
  wp_apply wp_pointer_plus _ _ _ ⟨by omega, by omega⟩
  wp_func_call
  wp_call
  have h1 : ¬ sint.Z j < 0 := by omega
  have h2 : ¬ (base +ₗ sint.Z off = null) := by
    intro h; rw [h] at H1; simp [null] at H1
  have h3 : ¬ (2 ^ 64 < base.addr + sint.Z off + sint.Z j * ((1 : Nat) : Int)) := by
    simp only [Loc.add, maxAddr] at H2; omega
  simp only [h1, h2, h3, ↓reduceIte]
  wp_auto
  simp only [show 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z j ∧ sint.Z j ≤ sint.Z j from
    ⟨H3, H4, Int.le_refl _⟩]
  wp_auto
  simp only [slice.fullSlice]
  rw [sliceIndexRef_byte _ _ H1 H3]
  iapply HΦ
  itrivial

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
