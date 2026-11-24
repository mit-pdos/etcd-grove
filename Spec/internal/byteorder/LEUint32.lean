/-
`byteorder.LEUint32(b)` (`internal/byteorder`, go1.27.3 `byteorder.go`): the little-endian `uint32` of
`b[0:4]`, after an early bounds check (`_ = b[3]`). Proved in `Proof/internal/byteorder/LEUint32.lean`,
over Perennial's translation (since its pin b3f2fc485; Perennial has no spec of it).
Lean-first (crc32-hooks2, 2026-11-22: `hash/crc32`'s `slicingUpdate`).
-/
module

public import Perennial.Proof.internal.byteorder.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- The little-endian `uint32` of four bytes. -/
def byteorder.le32 (b0 b1 b2 b3 : w8) : w32 :=
  b0.zeroExtend 32 ||| (b1.zeroExtend 32 <<< 8) ||| (b2.zeroExtend 32 <<< 16) ||| (b3.zeroExtend 32 <<< 24)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.internal.byteorder.Assumptions]

/-- `LEUint32(b)` on a slice of at least 4 bytes: the little-endian value of its first four. -/
abbrev byteorder.LEUint32.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (b0 b1 b2 b3 : w8) (rest : List w8),
  {{ (b ↦*{dq} (b0 :: b1 :: b2 :: b3 :: rest) : IProp GF) }}
    (App (Val (@! _root_.Perennial.internal.byteorder.LEUint32)) (Val #b))
  {{ RET #(byteorder.le32 b0 b1 b2 b3); b ↦*{dq} (b0 :: b1 :: b2 :: b3 :: rest) }}

end spec

end EtcdGrove
end Perennial
