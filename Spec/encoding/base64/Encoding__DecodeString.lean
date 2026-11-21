/-
`(*Encoding).DecodeString(s)` (`encoding/base64`, go1.27.3 `base64.go`), for a padded encoding
(`padChar` `=`): a fresh slice of the decoded bytes and an error, `nil` on padded base64 text over the
encoding's alphabet (`decOk`, `b64Ok`).
Proved in `Proof/encoding/base64/Encoding__DecodeString.lean`. Lean-first (prove-authcrypto, 2026-11-21).
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

/-- `e.DecodeString(s)` (`e` padded with `=`). -/
abbrev base64.Encoding.DecodeString.spec : Prop :=
  ∀ (e : Loc) (enc : _root_.Perennial.encoding.base64.Encoding) (dqe : DFrac) (s : GoString),
  enc.padChar' = W32 61 → enc.strict' = false → enc.decodeMap'.arr.length = 256 →
  {{ (e ↦{dqe} enc : IProp GF) }}
    (App (Val (e @!! go.GoType.PointerType _root_.Perennial.encoding.base64.Encoding.ty @!! go!"DecodeString")) (Val #s))
  {{ (b : GoSlice) (err : GoInterface), RET (PairV #b #err);
      ∃ bs : List w8, e ↦{dqe} enc ∗ b ↦* bs ∗
      ⌜base64.decOk enc → base64.b64Ok enc.encode'.arr s → err = GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
