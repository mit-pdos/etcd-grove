/-
`(*Encoding).EncodedLen(n)` (`encoding/base64`, go1.27.3 `base64.go`): the length of the encoding of
`n` bytes, for `0 ≤ n < 2^62` (beyond, Go's `(n + 2) / 3 * 4` overflows). Proved in
`Proof/encoding/base64/Encoding__EncodedLen.lean`. Lean-first.
-/
module

public import Proof.encoding.base64.Defs

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

/-- `e.EncodedLen(n)`: `encLen` of `n` for `e`'s padding. -/
abbrev base64.Encoding.EncodedLen.spec : Prop :=
  ∀ (e : Loc) (enc : _root_.Perennial.encoding.base64.Encoding) (dqe : DFrac) (n : w64),
  0 ≤ sint.Z n → sint.Z n < 2 ^ 62 →
  {{ (e ↦{dqe} enc : IProp GF) }}
    (App (Val (e @!! go.GoType.PointerType _root_.Perennial.encoding.base64.Encoding.ty @!!
      go!"EncodedLen")) (Val #n))
  {{ RET #(W64 (base64.encLen (base64.padOf enc.padChar') (sint.nat n) : Int)); e ↦{dqe} enc }}

end spec

end EtcdGrove
end Perennial
