/-
`getU64(b)` on a slice starting with 8 bytes `bs`: their little-endian value (`b` read, any
fraction). Proved in `Net/Proof/net/rpc/getU64.lean`; dsverify's `wp_getU64`, generalized to a
longer slice (the model reads a header's sequence number off its payload).
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
abbrev getU64.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs rem : List w8), bs.length = 8 →
  {{ (b ↦*{dq} (bs ++ rem) : IProp GF) }}
    (App (Val (@! net.rpc.getU64)) (Val #b))
  {{ RET #(leToU64 bs); b ↦*{dq} (bs ++ rem) }}

end spec

end net.rpc
end Perennial
