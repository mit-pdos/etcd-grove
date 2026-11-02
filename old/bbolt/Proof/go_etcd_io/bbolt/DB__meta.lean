module
public import Spec.go_etcd_io.bbolt.DB__meta
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

-- `hash.Hash64`'s type, which `Meta.Validate`'s spec takes: bbolt reaches `hash` only through
-- `hash/fnv`, so its `Assumptions` do not include `hash`'s
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

theorem DB.meta.wp_proof (hTxid : Meta.Txid.spec (GF := GF) (hG := hG))
    (hValidate : Meta.Validate.spec (GF := GF) (hG := hG)) :
    DB.meta.spec (GF := GF) (hG := hG) := by
  intro dbl m0 m1 dq dq0 dq1 v0 v1 Hc0 Hc1 Hval
  wp_start as ⟨Hf0, Hf1, H0, H1⟩
  wp_auto
  wp_apply hTxid m1 v1 dq1 $$ [H1] as H1
  · iframe
  wp_apply hTxid m0 v0 dq0 $$ [H0] as H0
  · iframe
  try wp_auto
  wp_if_destruct
  · try wp_auto
    wp_apply hValidate m1 v1 dq1 Hc1 $$ [H1] as %e ⟨H1, %He⟩
    · iframe
    try wp_auto
    cases e with
    | nil =>
      have Hv1 : metaValid v1 := He.1.1 rfl
      have Hp : metaPick v0 v1 = true := by unfold metaPick; simp [Hif, Hv1]
      try wp_auto
      simp only [Hp, ↓reduceIte]
      iapply HΦ; iframe; ipureintro; simpa using Hv1
    | ok i =>
      have Hv1 : ¬ metaValid v1 := fun h => nomatch He.1.2 h
      have Hv0 : metaValid v0 := Hval.resolve_right Hv1
      have Hp : metaPick v0 v1 = false := by unfold metaPick; simp [Hif, Hv1]
      try wp_auto
      wp_apply hValidate m0 v0 dq0 Hc0 $$ [H0] as %e ⟨H0, %He0⟩
      · iframe
      try wp_auto
      cases e with
      | nil =>
        try wp_auto
        simp only [Hp, Bool.false_eq_true, ↓reduceIte]
        iapply HΦ; iframe; ipureintro; simpa using Hv0
      | ok i0 => exact absurd (He0.1.2 Hv0) (by simp)
  · try wp_auto
    wp_apply hValidate m0 v0 dq0 Hc0 $$ [H0] as %e ⟨H0, %He⟩
    · iframe
    try wp_auto
    cases e with
    | nil =>
      have Hv0 : metaValid v0 := He.1.1 rfl
      have Hp : metaPick v0 v1 = false := by unfold metaPick; simp [Hif, Hv0]
      try wp_auto
      simp only [Hp, Bool.false_eq_true, ↓reduceIte]
      iapply HΦ; iframe; ipureintro; exact Hv0
    | ok i =>
      have Hv0 : ¬ metaValid v0 := fun h => nomatch He.1.2 h
      have Hv1 : metaValid v1 := Hval.resolve_left Hv0
      have Hp : metaPick v0 v1 = true := by unfold metaPick; simp [Hif, Hv0]
      try wp_auto
      wp_apply hValidate m1 v1 dq1 Hc1 $$ [H1] as %e ⟨H1, %He1⟩
      · iframe
      try wp_auto
      cases e with
      | nil =>
        try wp_auto
        simp only [Hp, ↓reduceIte]
        iapply HΦ; iframe; ipureintro; exact Hv1
      | ok i1 => exact absurd (He1.1.2 Hv1) (by simp)

end proof

end bbolt
end EtcdGrove
end Perennial
