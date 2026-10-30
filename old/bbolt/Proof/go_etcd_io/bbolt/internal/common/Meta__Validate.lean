module
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Validate
public import Proof.go_etcd_io.bbolt.internal.common.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]
-- `hash.Hash64`'s type (its underlying interface): `internal/common` reaches `hash` only
-- through `hash/fnv`, so its `Assumptions` do not include `hash`'s
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

theorem Meta.Validate.wp_proof (hSum : Meta.Sum64.spec (GF := GF) (hG := hG)) :
    Meta.Validate.spec (GF := GF) (hG := hG) := by
  intro l v dq Hc
  wp_start as Hl
  ihave #Hei : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors) $$ []
  · iPkgInit
  wp_auto
  by_cases Hm : v.magic' = W32 3977042669
  · rw [decide_eq_true Hm]
    try wp_auto
    by_cases Hv : v.version' = W32 2
    · rw [decide_eq_true Hv]
      try wp_auto
      wp_apply hSum l v dq Hc $$ [$Hl] as Hl
      by_cases Hs : v.checksum' = fnv64a ((metaBytes v).take 56)
      · rw [decide_eq_true Hs]
        try wp_auto
        iapply HΦ; iframe; ipureintro
        exact ⟨⟨fun _ => ⟨Hm, Hv, Hs⟩, fun _ => rfl⟩, Or.inl rfl⟩
      · rw [decide_eq_false Hs]
        try wp_auto
        icases bboltError_access go_etcd_io.bbolt.errors.ErrChecksum (by simp [bboltErrorNames])
          $$ Hei with ⟨%e, #He, %Hne⟩
        try wp_auto
        iapply HΦ; iframe; ipureintro
        obtain ⟨t, p, rfl⟩ := Hne
        exact ⟨⟨fun h => (by cases h), fun h => absurd h.2.2 Hs⟩, Or.inr ⟨t, p, rfl⟩⟩
    · rw [decide_eq_false Hv]
      try wp_auto
      icases bboltError_access go_etcd_io.bbolt.errors.ErrVersionMismatch (by simp [bboltErrorNames])
        $$ Hei with ⟨%e, #He, %Hne⟩
      try wp_auto
      iapply HΦ; iframe; ipureintro
      obtain ⟨t, p, rfl⟩ := Hne
      exact ⟨⟨fun h => (by cases h), fun h => absurd h.2.1 Hv⟩, Or.inr ⟨t, p, rfl⟩⟩
  · rw [decide_eq_false Hm]
    try wp_auto
    icases bboltError_access go_etcd_io.bbolt.errors.ErrInvalid (by simp [bboltErrorNames])
      $$ Hei with ⟨%e, #He, %Hne⟩
    try wp_auto
    iapply HΦ; iframe; ipureintro
    obtain ⟨t, p, rfl⟩ := Hne
    exact ⟨⟨fun h => (by cases h), fun h => absurd h.1 Hm⟩, Or.inr ⟨t, p, rfl⟩⟩

end proof

end bbolt
end EtcdGrove
end Perennial
