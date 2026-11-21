/-
`putU64(b, x)`: `b` with `x`'s 8 bytes, little-endian, after it (a slice with its capacity,
owned whole). Proved in `Net/Proof/net/rpc/putU64.lean`; dsverify's `wp_putU64`.
-/
module

public import Net.Proof.net.rpc.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]

/-- See the file header. -/
abbrev putU64.spec : Prop :=
  ∀ (b : GoSlice) (vs : List w8) (x : w64),
  {{ (b ↦* vs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
    (App (App (Val (@! net.rpc.putU64)) (Val #b)) (Val #x))
  {{ (r : GoSlice), RET #r; r ↦* (vs ++ u64Le x) ∗ ownSliceCap w8 r (DFrac.own 1) }}

end spec

end net.rpc
end Perennial
