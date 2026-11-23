/-
The proof of `transferReader.parseTransferEncoding`
(`Net/Spec/net/http/transferReader__parseTransferEncoding.lean`): no `Transfer-Encoding`.
-/
module

public import Net.Spec.net.http.transferReader__parseTransferEncoding

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem transferReader.parseTransferEncoding.wp_proof :
    transferReader.parseTransferEncoding.spec (GF := GF) (hG := hG) := by
  intro t tr
  wp_start as ⟨Ht, Hm⟩
  try wp_auto
  wp_apply (wp_map_lookup2 (V := GoSlice) go.string (go.SliceType go.string) tr.Header' _
    go!"Transfer-Encoding" _) $$ Hm as Hm
  try wp_auto
  iapply HΦ
  iframe

end proof

end net.http
end Perennial
