/-
`putFrame(b, payload)`: `b` with `frameOf p` after it, `p` the payload's bytes (read, any
fraction, and kept). Proved in `Net/Proof/net/rpc/putFrame.lean`.
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
abbrev putFrame.spec : Prop :=
  ∀ (b : GoSlice) (vs : List w8) (pl : GoSlice) (dq : DFrac) (p : List w8),
  {{ (b ↦* vs ∗ ownSliceCap w8 b (DFrac.own 1) ∗ pl ↦*{dq} p : IProp GF) }}
    (App (App (Val (@! net.rpc.putFrame)) (Val #b)) (Val #pl))
  {{ (r : GoSlice), RET #r; r ↦* (vs ++ frameOf p) ∗ ownSliceCap w8 r (DFrac.own 1) ∗
      pl ↦*{dq} p }}

end spec

end net.rpc
end Perennial
