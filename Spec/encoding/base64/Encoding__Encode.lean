/-
`(*Encoding).Encode(dst, src)` (`encoding/base64`, go1.27.3 `base64.go`): writes the encoding of
`src`'s bytes (`b64Enc` over `e`'s alphabet and padding) into `dst`, here exactly as long as the
encoding (`EncodedLen(len(src))`, what `EncodeToString` allocates). Proved in
`Proof/encoding/base64/Encoding__Encode.lean`. Lean-first.
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

/-- `e.Encode(dst, src)`, `dst` as long as the encoding: `dst` holds the encoding. -/
abbrev base64.Encoding.Encode.spec : Prop :=
  ∀ (e : Loc) (enc : _root_.Perennial.encoding.base64.Encoding) (dqe : DFrac) (dst src : GoSlice)
    (out d : List w8) (dq : DFrac),
  out.length = base64.encLen (base64.padOf enc.padChar') d.length →
  {{ (e ↦{dqe} enc ∗ dst ↦* out ∗ src ↦*{dq} d : IProp GF) }}
    (App (App (Val (e @!! go.GoType.PointerType _root_.Perennial.encoding.base64.Encoding.ty @!!
      go!"Encode")) (Val #dst)) (Val #src))
  {{ RET #(); e ↦{dqe} enc ∗
      dst ↦* _root_.Perennial.encoding.base64.b64Enc enc.encode'.arr (base64.padOf enc.padChar') d ∗
      src ↦*{dq} d }}

end spec

end EtcdGrove
end Perennial
