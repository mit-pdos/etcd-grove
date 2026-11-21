/-
Proof of `Encoding.DecodedLen` over its translated body (`encoding/base64`, go1.27.3). Lean-first
(prove-authcrypto, 2026-11-21).
-/
module

public import Spec.encoding.base64.Encoding__DecodedLen
public import Spec.encoding.base64.decodedLen
public import Proof.encoding.base64.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.encoding.base64.Assumptions]

theorem base64.Encoding.DecodedLen.wp_proof
    (wp_decodedLen : base64.decodedLen.spec (GF := GF) (hG := hG)) :
    base64.Encoding.DecodedLen.spec (GF := GF) (hG := hG) := by
  intro e enc dqe n hn0
  wp_start as He
  icases base64.enc_open e enc dqe $$ He with ⟨%Hnn, Hf⟩
  icases Hf with ⟨Henc, Hdm, Hpad, Hstrict⟩
  try wp_auto
  wp_apply (wp_decodedLen n enc.padChar' hn0)
  try wp_auto
  iapply HΦ
  iapply base64.enc_close e enc dqe Hnn
  unfold base64.encFields
  iframe

end proof

end EtcdGrove
end Perennial
