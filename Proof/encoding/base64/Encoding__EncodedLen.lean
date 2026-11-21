/-
The proof of `Spec/encoding/base64/Encoding__EncodedLen.lean`. Lean-first.
-/
module

public import Spec.encoding.base64.Encoding__EncodedLen
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

theorem base64.Encoding.EncodedLen.wp_proof :
    base64.Encoding.EncodedLen.spec (GF := GF) (hG := hG) := by
  intro e enc dqe n hn0 hn1
  wp_start as He
  try wp_auto
  icases base64.enc_open e enc dqe $$ He with ⟨%Hnn, Hf⟩
  icases Hf with ⟨Henc, Hdm, Hpad, Hstrict⟩
  try wp_auto
  wp_if_destruct
  · try wp_auto
    have h : BitVec.sdiv n (W64 3) * W64 4 + BitVec.sdiv (BitVec.srem n (W64 3) * W64 8 + W64 5) (W64 6) =
        W64 (base64.encLen (base64.padOf enc.padChar') (sint.nat n) : Int) := by
      simp only [base64.padOf, Hif, ite_true]
      exact base64.encLen_nopad_eq n hn0 hn1
    rw [h]
    iapply HΦ
    iapply base64.enc_close e enc dqe Hnn
    unfold base64.encFields
    iframe
  · try wp_auto
    have h : BitVec.sdiv (n + W64 2) (W64 3) * W64 4 =
        W64 (base64.encLen (base64.padOf enc.padChar') (sint.nat n) : Int) := by
      simp only [base64.padOf, Hif, ite_false]
      exact base64.encLen_pad_eq _ n hn0 hn1
    rw [h]
    iapply HΦ
    iapply base64.enc_close e enc dqe Hnn
    unfold base64.encFields
    iframe

end proof

end EtcdGrove
end Perennial
