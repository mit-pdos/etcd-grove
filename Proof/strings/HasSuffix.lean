/-
`strings.HasSuffix`, proved over Perennial's translation of Go's (`internal/stringslite.HasSuffix`).
-/
module

public import Spec.strings.HasSuffix
public import Perennial.Proof.strings.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.strings.Assumptions]

theorem strings.HasSuffix.wp_proof : strings.HasSuffix.spec (GF := GF) (hG := hG) := by
  intro s suf
  iintro %Φ #Hpkg HΦ
  wp_apply _root_.Perennial.strings.wp_HasSuffix
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
