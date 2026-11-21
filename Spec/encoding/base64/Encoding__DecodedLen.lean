/-
`(*Encoding).DecodedLen(n)` (`encoding/base64`, go1.27.3 `base64.go`): `decodedLen(n, enc.padChar)`.
Proved in `Proof/encoding/base64/Encoding__DecodedLen.lean`. Lean-first (prove-authcrypto, 2026-11-21).
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

/-- `e.DecodedLen(n)`: `decLen` of `n` for `e`'s padding. -/
abbrev base64.Encoding.DecodedLen.spec : Prop :=
  ∀ (e : Loc) (enc : _root_.Perennial.encoding.base64.Encoding) (dqe : DFrac) (n : w64),
  0 ≤ sint.Z n →
  {{ (e ↦{dqe} enc : IProp GF) }}
    (App (Val (e @!! go.GoType.PointerType _root_.Perennial.encoding.base64.Encoding.ty @!! go!"DecodedLen")) (Val #n))
  {{ RET #(W64 (base64.decLen enc.padChar' (sint.nat n) : Int)); e ↦{dqe} enc }}

end spec

end EtcdGrove
end Perennial
