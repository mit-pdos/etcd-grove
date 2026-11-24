/-
`byteorder.BEPutUint64(b, v)` (`internal/byteorder`, go1.27.3 `byteorder.go`): stores `v` big-endian
into `b[0:8]`, after an early bounds check (`_ = b[7]`). Proved in
`Proof/internal/byteorder/BEPutUint64.lean` from Perennial's stronger
`internal.byteorder.BEPutUint64.spec` (Perennial's translation of `internal/byteorder` since its pin
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

/-- `BEPutUint64(b, v)` on a slice of at least 8 bytes: the slice keeps its length (its first 8 bytes
are `v`'s, which the callers here do not read). -/
abbrev byteorder.BEPutUint64.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (v : w64), 8 ≤ bs.length →
  {{ (b ↦* bs : IProp GF) }}
    (App (App (Val (@! _root_.Perennial.internal.byteorder.BEPutUint64)) (Val #b)) (Val #v))
  {{ RET #(); ∃ bs' : List w8, b ↦* bs' ∗ ⌜bs'.length = bs.length⌝ }}

end spec

end EtcdGrove
end Perennial
