/-
The proof of `Spec/google_golang_org/grpc/encodeMetadataHeader.lean`: the `-bin` suffix (Perennial's
`strings.HasSuffix`), then `[]byte(v)` and `encodeBinHeader`.
-/
module

public import Spec.google_golang_org.grpc.encodeMetadataHeader
public import Spec.google_golang_org.grpc.encodeBinHeader
public import Perennial.Spec.strings.HasSuffix

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.Assumptions]

theorem grpc.encodeMetadataHeader.wp_proof
    (wp_HasSuffix : _root_.Perennial.strings.HasSuffix.spec (GF := GF) (hG := hG))
    (wp_encodeBinHeader : grpc.encodeBinHeader.spec (GF := GF) (hG := hG)) :
    grpc.encodeMetadataHeader.spec (GF := GF) (hG := hG) := by
  intro k v
  wp_start as #Hpkg
  unfold grpcHdr.encMdHdr
  wp_auto
  wp_apply (wp_HasSuffix k go!"-bin")
  wp_if_destruct
  · simp only [Hif, ↓reduceIte]
    wp_apply (wp_string_to_bytes v) as %sl ⟨Hsl, -⟩
    wp_apply (wp_encodeBinHeader sl (DFrac.own 1) v) $$ [Hsl] as -
    · iframe
    iapply HΦ; itrivial
  · simp only [Hif, ↓reduceIte]
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
