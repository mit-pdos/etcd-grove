/-
`(*types.ID).String` (the pointer-receiver wrapper of `ID.String`: a load, then the call),
verified over `ID.String`'s spec. Until 2026-11-18 a trust-boundary axiom (unit N4, 2026-10-17).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.types.Assumptions]

theorem types.ID.String_ptr.wp_proof (wp_String : types.ID.String.spec (GF := GF) (hG := hG)) :
    types.ID.String_ptr.spec (GF := GF) (hG := hG) := by
  intro p dq id
  wp_start as Hp
  wp_auto
  haveI : go.NotInterface go.uint64 := ⟨by unfold go.uint64; trivial⟩
  (try wp_auto)
  wp_apply wp_String as %s %Hs
  iapply HΦ
  iframe
  ipureintro; exact Hs

end proof

end EtcdGrove
end Perennial
