/-
`(*Page).BranchPageElement`'s proof (`internal/common/page.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElement
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeIndex

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

theorem Page.BranchPageElement.wp_proof
    (wp_UnsafeIndex : UnsafeIndex.spec (GF := GF) (hG := hG)) :
    Page.BranchPageElement.spec (GF := GF) (hG := hG) := by
  intro l idx H1 H2
  wp_start
  wp_auto
  have hz : sint.Z (W64 16 + W64 (uint.Z idx) * W64 16) = 16 + 16 * uint.Z idx := by
    have := idx.isLt; simp only [uint.Z] at *; word
  have hi : 0 ≤ uint.Z idx := by simp [uint.Z]
  wp_apply wp_UnsafeIndex
  · ipureintro; rw [hz]; simp only [Loc.add]; omega
  · ipureintro; rw [hz]; simp only [Loc.add]; omega
  rw [hz]
  iapply HΦ
  itrivial

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
