/-
`SetCodec(c)` with no codec registered yet (`codecUnset`) and `c` a codec meeting `C`: registers
it (`codecSet C`, for good). Proved in `Net/Proof/net/rpc/SetCodec.lean`.
-/
module

public import Net.Proof.net.rpc.Codec

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
abbrev SetCodec.spec : Prop :=
  ∀ (C : CodecSpec GF) (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
      sync.isMutex (globalAddr net.rpc.codecMu) (codecInv (GF := GF)) ∗ codecUnset ∗
      codecIs C c ∗ ⌜c ≠ null⌝ }}
    (App (Val (@! net.rpc.SetCodec)) (Val #c))
  {{ RET #(); codecSet C }}

end spec

end net.rpc
end Perennial
