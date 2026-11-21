/-
`assemble32(n1, n2, n3, n4)` (`encoding/base64`, go1.27.3 `base64.go`): the four 6-bit digits
assembled, accepted unless one of them is `0xff` (their OR is).
Proved in `Proof/encoding/base64/assemble32.lean`. Lean-first (prove-authcrypto, 2026-11-21).
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

/-- `assemble32(n1, n2, n3, n4)`: some word, and `ok` exactly when the digits' OR is not `0xff`. -/
abbrev base64.assemble32.spec : Prop :=
  ∀ (n1 n2 n3 n4 : w8),
  {{ (True : IProp GF) }}
    (App (App (App (App (Val (@! _root_.Perennial.encoding.base64.assemble32)) (Val #n1)) (Val #n2))
      (Val #n3)) (Val #n4))
  {{ (dn : w32) (ok : Bool), RET (PairV #dn #ok); ⌜ok = !decide (n1 ||| n2 ||| n3 ||| n4 = W8 255)⌝ }}

end spec

end EtcdGrove
end Perennial
