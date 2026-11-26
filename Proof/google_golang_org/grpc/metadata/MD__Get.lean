/-
Proof of `Spec/google_golang_org/grpc/metadata/MD__Get.lean` over the real body (2026-11-18; it was
a trust-boundary axiom while grpc's `metadata` was names-only): `md[strings.ToLower(k)]`, over
`strings.ToLower`'s spec. Lean-first.
-/
module

public import Spec.google_golang_org.grpc.metadata.MD__Get
public import Spec.strings.ToLower

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode google_golang_org.grpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.metadata.Assumptions]

theorem metadata.MD.Get.wp_proof
    (wp_ToLower : strings.ToLower.spec (GF := GF) (hG := hG)) :
    metadata.MD.Get.spec (GF := GF) (hG := hG) := by
  intro l md m k
  wp_start as ⟨#Hl, Hm⟩
  haveI : go.NotInterface (go.GoType.MapType go.string (go.GoType.SliceType go.string)) :=
    ⟨trivial⟩
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (wp_ToLower k) as %k' %hk'
  (try wp_auto)
  wp_apply wp_map_lookup1 go.string (go.GoType.SliceType go.string) md m k' DfracDiscarded
    $$ [$Hm] as -
  (try wp_auto)
  iapply HΦ
  ipureintro
  refine ⟨k', hk', ?_⟩
  cases h : m !! k' with
  | none => left; exact ⟨rfl, rfl⟩
  | some sl => right; simp [h]

end proof

end EtcdGrove
end Perennial
