/-
`decodedLen(n, padChar)` (`encoding/base64`, go1.27.3 `base64.go`): the most bytes `n` bytes of
base64 decode to, for `0 ≤ n` (no overflow: `n / 4 * 3 < 2^63`).
Proved in `Proof/encoding/base64/decodedLen.lean`. Lean-first (prove-authcrypto, 2026-11-21).
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

/-- `decodedLen(n, p)`: `decLen p n`. -/
abbrev base64.decodedLen.spec : Prop :=
  ∀ (n : w64) (p : w32), 0 ≤ sint.Z n →
  {{ (True : IProp GF) }}
    (App (App (Val (@! _root_.Perennial.encoding.base64.decodedLen)) (Val #n)) (Val #p))
  {{ RET #(W64 (base64.decLen p (sint.nat n) : Int)); True }}

end spec

end EtcdGrove
end Perennial
