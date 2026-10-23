/-
Lean-first (no Rocq counterpart). The proof of `runtime.Encode`: a zero `bytes.Buffer` (empty,
`ownBuffer_new`), the encoder's `Encode` on it, then `Bytes()`.
-/
module

public import Spec.k8s_io.apimachinery.pkg.runtime.Encode
public import Spec.bytes.Buffer__Bytes

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode bufferM

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.runtime.Assumptions]
variable [_root_.Perennial.bytes.Assumptions]

theorem runtime.Encode.wp_proof (wp_Bytes : bytes.Buffer.Bytes.spec (GF := GF) (hG := hG)) :
    runtime.Encode.spec (GF := GF) (hG := hG) := by
  intro ei x P Q bs
  wp_start as ⟨HP, Henc⟩
  ihave #Pby : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  (try wp_auto)
  ihave Hb := ownBuffer_new «$r0_ptr» $$ «$r0»
  ispecialize Henc $$ %«$r0_ptr»
  wp_apply Henc $$ [$HP] [$Hb] as ⟨Hb, HQ⟩
  (try wp_auto)
  wp_apply wp_Bytes $$ [$Hb] as %sl Hsl
  (try wp_auto)
  iapply HΦ
  iframe Hsl HQ
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
