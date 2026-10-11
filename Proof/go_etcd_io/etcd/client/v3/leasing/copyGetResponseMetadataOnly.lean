/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/copyGetResponseMetadataOnly.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.copyGetResponseMetadataOnly
public import Spec.go_etcd_io.etcd.client.v3.leasing.copyHeader

@[expose] public section

set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem copyGetResponseMetadataOnly.wp_proof (hcopy : copyHeader.spec (GF := GF) (hG := hG)) :
    copyGetResponseMetadataOnly.spec (GF := GF) (hG := hG) := by
  intro e dq
  wp_start as Hr
  unfold respOwn
  icases Hr with ⟨%hnn, HH, #Hhdr, HK, HKs, Hcap, Hkvs, HM, HC⟩
  wp_auto
  rw [decide_eq_false hnn]
  wp_auto
  ihave %Hhnn : ⌜e.hdr ≠ null⌝ $$ [Hhdr]
  · unfold hdrFull; icases Hhdr with ⟨%h, -⟩; ipureintro; exact h
  wp_apply hcopy $$ [] as %h' Hh'
  · unfold headerOk; simp only [Hhnn, ↓reduceIte]; iexact Hhdr
  icases Hh' with (⟨%Hbad, -⟩ | ⟨-, #Hh'⟩)
  · exact absurd Hbad Hhnn
  wp_auto
  wp_alloc r as Hr
  ihave %Hrnn := typedPointsto_not_null $$ Hr
  iStructNamed Hr
  wp_auto
  iapply HΦ
  isplitl [HH HK HKs Hcap Hkvs HM HC]
  · iframe; iframe #; ipureintro; exact hnn
  isplitr
  · ipureintro; exact Hrnn
  iexists h'
  iframe
  iframe #

end proof

end leasing
end EtcdGrove
end Perennial
