/-
`(*Page).FastCheck`'s proof (`internal/common/page.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Page__FastCheck
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsValidPage

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

theorem Page.FastCheck.wp_proof
    (wp_Page_IsValidPage : Page.IsValidPage.spec (GF := GF) (hG := hG)) :
    Page.FastCheck.spec (GF := GF) (hG := hG) := by
  intro l v dq id Hid Hvalid
  wp_start as Hl
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
  iStructNamedPrefix Hl "f_"
  wp_auto
  rw [decide_eq_true Hid]
  wp_auto
  ihave Hl : l ↦{dq} v $$ [f_id f_flags f_count f_overflow]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_apply wp_Page_IsValidPage $$ [$Hl] as Hl
  rw [decide_eq_true Hvalid]
  wp_auto
  iapply HΦ; iframe

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
