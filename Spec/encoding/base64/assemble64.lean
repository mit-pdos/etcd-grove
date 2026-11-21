/-
`assemble64(n1, ..., n8)` (`encoding/base64`, go1.27.3 `base64.go`): the eight 6-bit digits
assembled, accepted unless one of them is `0xff` (their OR is).
Proved in `Proof/encoding/base64/assemble64.lean`. Lean-first (prove-authcrypto, 2026-11-21).
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

/-- `assemble64(n1, ..., n8)`: some word, and `ok` exactly when the digits' OR is not `0xff`. -/
abbrev base64.assemble64.spec : Prop :=
  ∀ (n1 n2 n3 n4 n5 n6 n7 n8 : w8),
  {{ (True : IProp GF) }}
    (App (App (App (App (App (App (App (App (Val (@! _root_.Perennial.encoding.base64.assemble64))
      (Val #n1)) (Val #n2)) (Val #n3)) (Val #n4)) (Val #n5)) (Val #n6)) (Val #n7)) (Val #n8))
  {{ (dn : w64) (ok : Bool), RET (PairV #dn #ok);
      ⌜ok = !decide (n1 ||| n2 ||| n3 ||| n4 ||| n5 ||| n6 ||| n7 ||| n8 = W8 255)⌝ }}

end spec

end EtcdGrove
end Perennial
