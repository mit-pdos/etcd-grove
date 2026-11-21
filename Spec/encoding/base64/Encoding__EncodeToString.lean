/-
`(*Encoding).EncodeToString(src)` (`encoding/base64`, go1.27.3 `base64.go`): the encoding of `src`'s
bytes (`b64Enc` over `e`'s alphabet and padding), `src` read and kept. No premise on `src`'s length:
its bytes are in memory, so there are at most `2^47` of them (`maxAddr`), far below where
`EncodedLen`'s `(n + 2) / 3 * 4` overflows (`n ≥ 3·2^61`). Proved in
`Proof/encoding/base64/Encoding__EncodeToString.lean`. Lean-first.
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

/-- `e.EncodeToString(src)`: the encoding of `src`'s bytes. -/
abbrev base64.Encoding.EncodeToString.spec : Prop :=
  ∀ (e : Loc) (enc : _root_.Perennial.encoding.base64.Encoding) (dqe : DFrac) (src : GoSlice)
    (d : List w8) (dq : DFrac),
  {{ (e ↦{dqe} enc ∗ src ↦*{dq} d : IProp GF) }}
    (App (Val (e @!! go.GoType.PointerType _root_.Perennial.encoding.base64.Encoding.ty @!!
      go!"EncodeToString")) (Val #src))
  {{ RET #(_root_.Perennial.encoding.base64.b64Enc enc.encode'.arr (base64.padOf enc.padChar') d);
      e ↦{dqe} enc ∗ src ↦*{dq} d }}

end spec

end EtcdGrove
end Perennial
