/-
The proof of `Spec/encoding/base64/Encoding__EncodeToString.lean`: a buffer of `EncodedLen(len(src))`
bytes (`src`'s length is at most `2^47`, `base64.bytes_len_le`), `Encode` into it, its string.
Lean-first.
-/
module

public import Spec.encoding.base64.Encoding__EncodeToString
public import Spec.encoding.base64.Encoding__EncodedLen
public import Spec.encoding.base64.Encoding__Encode
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

theorem base64.Encoding.EncodeToString.wp_proof
    (wp_EncodedLen : base64.Encoding.EncodedLen.spec (GF := GF) (hG := hG))
    (wp_Encode : base64.Encoding.Encode.spec (GF := GF) (hG := hG)) :
    base64.Encoding.EncodeToString.spec (GF := GF) (hG := hG) := by
  intro e enc dqe src d dq
  wp_start as ⟨He, Hsrc⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hsrc
  ihave %Hb := base64.bytes_len_le _ _ _ $$ Hsrc
  have h0 : 0 ≤ sint.Z src.len := Hsl.2
  have h62 : sint.Z src.len < 2 ^ 62 := by have := Hsl.1; word
  try wp_auto
  wp_apply (wp_EncodedLen e enc dqe src.len h0 h62) $$ He as He
  try wp_auto
  have hn : d.length = sint.nat src.len := Hsl.1
  have hL : base64.encLen (base64.padOf enc.padChar') (sint.nat src.len) < 2 ^ 50 := by
    unfold base64.encLen; split <;> omega
  have hLz : sint.Z (W64 (base64.encLen (base64.padOf enc.padChar') (sint.nat src.len) : Int)) =
      base64.encLen (base64.padOf enc.padChar') (sint.nat src.len) := by word
  wp_apply (wp_slice_make2 (V := w8) _) $$ [] as %buf ⟨Hbuf, _⟩
  · ipureintro; rw [hLz]; omega
  try wp_auto
  have hout : (List.replicate (sint.nat (W64 (base64.encLen (base64.padOf enc.padChar')
      (sint.nat src.len) : Int))) (zero_val w8)).length =
      base64.encLen (base64.padOf enc.padChar') d.length := by
    have : sint.nat (W64 (base64.encLen (base64.padOf enc.padChar') (sint.nat src.len) : Int)) =
        base64.encLen (base64.padOf enc.padChar') (sint.nat src.len) := by word
    rw [List.length_replicate, hn, this]
  wp_apply (wp_Encode e enc dqe buf src _ d dq hout) $$ [He Hbuf Hsrc] as ⟨He, Hbuf, Hsrc⟩
  · iframe
  try wp_auto
  wp_apply wp_bytes_to_string _ _ _ $$ Hbuf as Hbuf
  try wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
