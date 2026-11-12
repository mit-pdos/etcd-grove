/-
`(*branchPageElement).Pos`'s proof (`internal/common/page.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Pos

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem branchPageElement.Pos.wp_proof : branchPageElement.Pos.spec (GF := GF) (hG := hG) := by
  intro l v dq
  wp_start as Hl
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
  iStructNamed Hl
  wp_auto
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
