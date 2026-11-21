/-
`putString(b, s)`: `b` with `strEnc s` after it (`s`'s length, 8 bytes, then its bytes).
Proved in `Net/Proof/net/rpc/putString.lean`.
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
abbrev putString.spec : Prop :=
  ∀ (b : GoSlice) (vs : List w8) (s : GoString),
  {{ (b ↦* vs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
    (App (App (Val (@! net.rpc.putString)) (Val #b)) (Val #s))
  {{ (r : GoSlice), RET #r; r ↦* (vs ++ strEnc s) ∗ ownSliceCap w8 r (DFrac.own 1) }}

end spec

end net.rpc
end Perennial
