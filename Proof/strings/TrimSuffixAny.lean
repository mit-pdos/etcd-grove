/-
**`strings.TrimSuffix` returns some string** (2026-10-24, the merge of the rafthttp work into
`lean`, whose spec gives the exact result): what `streamReader.dial` and `checkPostResponse`
need (they compare it with error messages). Lean-first.
-/
module

public import Spec.strings.TrimSuffix

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem strings.TrimSuffix.any (hT : strings.TrimSuffix.spec (GF := GF) (hG := hG))
    (s suffix : GoString) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions _root_.Perennial.strings.TrimSuffix [])) (Val #s)) (Val #suffix))
    {{ (r : GoString), RET #r; True }} := by
  iintro %Φ - HΦ
  wp_apply hT s suffix
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
