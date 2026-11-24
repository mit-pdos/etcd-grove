/-
`byteorder.BEPutUint32(b, v)` (`internal/byteorder`, go1.27.3 `byteorder.go`): stores `v` big-endian
into `b[0:4]`, after an early bounds check (`_ = b[3]`). Proved in
`Proof/internal/byteorder/BEPutUint32.lean` from Perennial's stronger
`internal.byteorder.BEPutUint32.spec` (Perennial's translation of `internal/byteorder` since its pin
b3f2fc485). Lean-first (prove-authcrypto, 2026-11-21).
-/
module

public import Perennial.Proof.internal.byteorder.Base

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
variable [package_sem : _root_.Perennial.internal.byteorder.Assumptions]

/-- `BEPutUint32(b, v)` on a slice of at least 4 bytes: the slice keeps its length (its first 4 bytes
are `v`'s, which the callers here do not read). -/
abbrev byteorder.BEPutUint32.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (v : w32), 4 ≤ bs.length →
  {{ (b ↦* bs : IProp GF) }}
    (App (App (Val (@! _root_.Perennial.internal.byteorder.BEPutUint32)) (Val #b)) (Val #v))
  {{ RET #(); ∃ bs' : List w8, b ↦* bs' ∗ ⌜bs'.length = bs.length⌝ }}

end spec

end EtcdGrove
end Perennial
