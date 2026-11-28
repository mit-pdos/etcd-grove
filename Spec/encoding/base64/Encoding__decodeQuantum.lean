/-
`(*Encoding).decodeQuantum(dst, src, si)` (`encoding/base64`, go1.27.3 `base64.go`): decodes one
quantum of `src` from `si` (up to four symbols, skipping newlines, with its padding) into `dst`, for a
padded, not strict encoding (`padChar` `=`). For any input it stays within `dst` when `dst` has room for three
bytes per four remaining input bytes, returns at most three bytes per four bytes consumed, and
without an error either decoded four symbols or reached the end. For an encoding that decodes padded
base64 (`decOk`), on the text from `si` without its newlines (`dropNL`): without an error it read one
quantum of it (`quantumOk`: four symbols, or the rest is padded base64 text and it read all of it);
with an error, that text is not padded base64 text (`b64Ok`).
Proved in `Proof/encoding/base64/Encoding__decodeQuantum.lean`. Lean-first (prove-authcrypto, 2026-11-21).
-/
module

public import Proof.encoding.base64.DecodeDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.encoding.base64.Assumptions]

/-- `e.decodeQuantum(dst, src, si)` (`e` padded with `=`): see the file's header. -/
abbrev base64.Encoding.decodeQuantum.spec : Prop :=
  ∀ (e : Loc) (enc : _root_.Perennial.encoding.base64.Encoding) (dqe : DFrac) (dst src : GoSlice) (d s : List w8)
    (dq : DFrac) (si : w64),
  enc.padChar' = W32 61 → enc.strict' = false → enc.decodeMap'.arr.length = 256 →
  0 ≤ sint.Z si → sint.Z si ≤ s.length → 3 * ((s.length - sint.nat si) / 4) ≤ d.length →
  {{ (e ↦{dqe} enc ∗ dst ↦* d ∗ src ↦*{dq} s : IProp GF) }}
    (App (App (App (Val (e @!! go.GoType.PointerType _root_.Perennial.encoding.base64.Encoding.ty @!! go!"decodeQuantum")) (Val #dst)) (Val #src)) (Val #si))
  {{ (si' ninc : w64) (err : GoInterface), RET (PairV (PairV #si' #ninc) #err);
      ∃ d' : List w8, e ↦{dqe} enc ∗ dst ↦* d' ∗ src ↦*{dq} s ∗
      ⌜d'.length = d.length ∧ sint.Z si ≤ sint.Z si' ∧ sint.Z si' ≤ s.length ∧
        0 ≤ sint.Z ninc ∧ sint.Z ninc ≤ 3 * ((sint.Z si' - sint.Z si) / 4) ∧
        (err = GoInterface.nil →
          (sint.Z ninc = 3 ∧ sint.Z si + 4 ≤ sint.Z si') ∨ sint.Z si' = s.length) ∧
        (base64.decOk enc →
          (err = GoInterface.nil →
            base64.quantumOk enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si)))
              (_root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si')))) ∧
          (err ≠ GoInterface.nil →
            ¬ base64.b64Ok enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL (s.drop (sint.nat si)))))⌝ }}

end spec

end EtcdGrove
end Perennial
