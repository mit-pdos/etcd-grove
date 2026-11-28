/-
What `encoding/base64`'s initializer (`Init.lean`, `etc/gen-init.py`) needs beyond the functions'
specs: the two alphabets are valid (`NewEncoding` does not panic on them), and the package fact's
parts (`stdEncInit`, `rawUrlEncInit`, `stdDecInit`) from the encodings the initializer builds and
`EncodeToString`'s and `DecodeString`'s specs. Lean-first.
-/
module

public import Spec.encoding.base64.Encoding__EncodeToString
public import Spec.encoding.base64.Encoding__DecodeString

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace base64

open Iris Iris.BI Iris.ProofMode

/-- `StdEncoding`'s alphabet is 64 distinct bytes, neither `\n` nor `\r`. -/
theorem stdAlphabet_ok :
    _root_.Perennial.encoding.base64.stdAlphabet.length = 64 ∧
      _root_.Perennial.encoding.base64.stdAlphabet.Nodup ∧
      (10 : w8) ∉ _root_.Perennial.encoding.base64.stdAlphabet ∧
      (13 : w8) ∉ _root_.Perennial.encoding.base64.stdAlphabet := by
  decide

/-- `URLEncoding`'s alphabet is 64 distinct bytes, neither `\n` nor `\r`. -/
theorem urlAlphabet_ok :
    _root_.Perennial.encoding.base64.urlAlphabet.length = 64 ∧
      _root_.Perennial.encoding.base64.urlAlphabet.Nodup ∧
      (10 : w8) ∉ _root_.Perennial.encoding.base64.urlAlphabet ∧
      (13 : w8) ∉ _root_.Perennial.encoding.base64.urlAlphabet := by
  decide

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.encoding.base64.Assumptions]

/-- `StdEncoding`'s part of the package fact, from the encoding it holds. -/
theorem stdEncInit_intro (wp_EncodeToString : base64.Encoding.EncodeToString.spec (GF := GF) (hG := hG))
    (e : Loc) (enc : _root_.Perennial.encoding.base64.Encoding)
    (h1 : enc.encode'.arr = _root_.Perennial.encoding.base64.stdAlphabet) (h2 : enc.padChar' = W32 61) :
    globalAddr _root_.Perennial.encoding.base64.StdEncoding ↦□ e -∗ e ↦□ enc -∗
      _root_.Perennial.encoding.base64.stdEncInit (GF := GF) := by
  iintro #Hg #He
  iexists e
  iframe Hg
  imodintro
  iintro %sl %dq %d %Φ Hsl HΦ
  have hp : base64.padOf enc.padChar' = some 61 := by rw [h2]; rfl
  unfold _root_.Perennial.encoding.base64.stdEnc
  iapply (wp_EncodeToString e enc DFrac.discard sl d dq) $$ [Hsl]
  · iframe; iexact He
  inext
  iintro ⟨-, Hsl⟩
  rw [h1, hp]
  iapply HΦ $$ Hsl

/-- `RawURLEncoding`'s part of the package fact, from the encoding it holds. -/
theorem rawUrlEncInit_intro
    (wp_EncodeToString : base64.Encoding.EncodeToString.spec (GF := GF) (hG := hG))
    (e : Loc) (enc : _root_.Perennial.encoding.base64.Encoding)
    (h1 : enc.encode'.arr = _root_.Perennial.encoding.base64.urlAlphabet) (h2 : enc.padChar' = W32 (-1)) :
    globalAddr _root_.Perennial.encoding.base64.RawURLEncoding ↦□ e -∗ e ↦□ enc -∗
      _root_.Perennial.encoding.base64.rawUrlEncInit (GF := GF) := by
  iintro #Hg #He
  iexists e
  iframe Hg
  imodintro
  iintro %sl %dq %d %Φ Hsl HΦ
  have hp : base64.padOf enc.padChar' = none := by rw [h2]; rfl
  unfold _root_.Perennial.encoding.base64.rawUrlEnc
  iapply (wp_EncodeToString e enc DFrac.discard sl d dq) $$ [Hsl]
  · iframe; iexact He
  inext
  iintro ⟨-, Hsl⟩
  rw [h1, hp]
  iapply HΦ $$ Hsl

/-- `RawStdEncoding`'s part of the package fact (phase 7 S2 core, 2026-11-23), from the encoding
it holds. -/
theorem rawStdEncInit_intro
    (wp_EncodeToString : base64.Encoding.EncodeToString.spec (GF := GF) (hG := hG))
    (e : Loc) (enc : _root_.Perennial.encoding.base64.Encoding)
    (h1 : enc.encode'.arr = _root_.Perennial.encoding.base64.stdAlphabet) (h2 : enc.padChar' = W32 (-1)) :
    globalAddr _root_.Perennial.encoding.base64.RawStdEncoding ↦□ e -∗ e ↦□ enc -∗
      _root_.Perennial.encoding.base64.rawStdEncInit (GF := GF) := by
  iintro #Hg #He
  iexists e
  iframe Hg
  imodintro
  iintro %sl %dq %d %Φ Hsl HΦ
  have hp : base64.padOf enc.padChar' = none := by rw [h2]; rfl
  unfold _root_.Perennial.encoding.base64.rawStdEnc
  iapply (wp_EncodeToString e enc DFrac.discard sl d dq) $$ [Hsl]
  · iframe; iexact He
  inext
  iintro ⟨-, Hsl⟩
  rw [h1, hp]
  iapply HΦ $$ Hsl

/-- `StdEncoding`'s decoder part of the package fact (prove-authcrypto, 2026-11-21), from the encoding
it holds (`NewEncoding`'s: the standard alphabet, padding `=`, its decode map, not strict). -/
theorem stdDecInit_intro (wp_DecodeString : base64.Encoding.DecodeString.spec (GF := GF) (hG := hG))
    (e : Loc) (enc : _root_.Perennial.encoding.base64.Encoding)
    (h1 : enc.encode'.arr = _root_.Perennial.encoding.base64.stdAlphabet) (h2 : enc.padChar' = W32 61)
    (h3 : enc.decodeMap'.arr = base64.dmAfter enc.encode'.arr 64) (h4 : enc.strict' = false) :
    globalAddr _root_.Perennial.encoding.base64.StdEncoding ↦□ e -∗ e ↦□ enc -∗
      _root_.Perennial.encoding.base64.stdDecInit (GF := GF) := by
  iintro #Hg #He
  iexists e
  iframe Hg
  imodintro
  iintro %s %Φ HΦ
  have hok : base64.decOk enc :=
    ⟨by rw [h1]; decide, by rw [h1]; decide, h3, h2, h4, by rw [h1]; decide, by rw [h1]; decide⟩
  iapply (wp_DecodeString e enc DFrac.discard s h2 h4 (base64.decOk_len hok)) $$ [He]
  · iexact He
  inext
  iintro %b %err ⟨%bs, -, Hb, %Herr⟩
  iapply HΦ $$ Hb
  ipureintro
  unfold _root_.Perennial.encoding.base64.stdDecOk
  rw [← h1]
  exact Herr hok

end facts

end base64
end EtcdGrove
end Perennial
