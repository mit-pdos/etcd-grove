/-
`(*Encoding).Decode(dst, src)` (`encoding/base64`, go1.27.3 `base64.go`), for a padded encoding
(`padChar` `=`) and a `dst` of at least `DecodedLen(len(src))` bytes (what the function documents):
for any input, the count of bytes written is within `dst`; for an encoding that decodes padded
base64 (`decOk`), the error is `nil` exactly when `src` without its newlines (`dropNL`) is padded
base64 text over the encoding's alphabet (`b64Ok`).
Proved in `Proof/encoding/base64/Encoding__Decode.lean`. Lean-first (prove-authcrypto, 2026-11-21).
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

/-- `e.Decode(dst, src)` (`e` padded with `=`, `dst` of `DecodedLen(len(src))` bytes or more). -/
abbrev base64.Encoding.Decode.spec : Prop :=
  ∀ (e : Loc) (enc : _root_.Perennial.encoding.base64.Encoding) (dqe : DFrac) (dst src : GoSlice) (d s : List w8) (dq : DFrac),
  enc.padChar' = W32 61 → enc.strict' = false → enc.decodeMap'.arr.length = 256 → 3 * (s.length / 4) ≤ d.length →
  {{ (e ↦{dqe} enc ∗ dst ↦* d ∗ src ↦*{dq} s : IProp GF) }}
    (App (App (Val (e @!! go.GoType.PointerType _root_.Perennial.encoding.base64.Encoding.ty @!! go!"Decode")) (Val #dst)) (Val #src))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ d' : List w8, e ↦{dqe} enc ∗ dst ↦* d' ∗ src ↦*{dq} s ∗
      ⌜d'.length = d.length ∧ 0 ≤ sint.Z n ∧ sint.Z n ≤ d.length ∧
        (base64.decOk enc →
          (err = GoInterface.nil ↔
            base64.b64Ok enc.encode'.arr (_root_.Perennial.encoding.base64.dropNL s)))⌝ }}

end spec

end EtcdGrove
end Perennial
