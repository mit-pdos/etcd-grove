/-
`(*leafPageElement).Key`'s proof (`internal/common/page.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Key
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeByteSlice

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

theorem leafPageElement.Key.wp_proof
    (wp_UnsafeByteSlice : UnsafeByteSlice.spec (GF := GF) (hG := hG)) :
    leafPageElement.Key.spec (GF := GF) (hG := hG) := by
  intro n e dq H1 H2
  wp_start as Hn
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %hnn⟩
  iStructNamed Hn
  wp_auto
  have hp := e.pos'.isLt
  have hk := e.ksize'.isLt
  have h0 : sint.Z (W64 0) = 0 := rfl
  have h1 : sint.Z (W64 (uint.Z e.pos')) = uint.Z e.pos' := by simp only [uint.Z] at *; word
  have h2 : sint.Z (W64 (uint.Z e.pos') + W64 (uint.Z e.ksize')) =
      uint.Z e.pos' + uint.Z e.ksize' := by simp only [uint.Z] at *; word
  wp_apply wp_UnsafeByteSlice
  · ipureintro; rw [h0, loc_add_0]; exact H1
  · ipureintro; rw [h0, h2, loc_add_0]; omega
  · ipureintro; rw [h1]; simp only [uint.Z] at *; omega
  · ipureintro; rw [h1, h2]; simp only [uint.Z] at *; omega
  rw [h0, h1, loc_add_0,
    show W64 (uint.Z e.pos') + W64 (uint.Z e.ksize') - W64 (uint.Z e.pos') = W64 (uint.Z e.ksize') by
      bv_omega]
  iapply HΦ
  iapply typedPointsto_combine _ _ _ hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
