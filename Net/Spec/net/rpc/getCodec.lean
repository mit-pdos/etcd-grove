/-
`getCodec()` after a codec meeting `C` is registered (`codecSet C`): the registered codec.
Proved in `Net/Proof/net/rpc/getCodec.lean`.
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
abbrev getCodec.spec : Prop :=
  ∀ (C : CodecSpec GF),
  {{ codecSet (GF := GF) C }}
    (App (Val (@! net.rpc.getCodec)) (Val #()))
  {{ (c : Loc), RET #c; codecIs C c }}

end spec

end net.rpc
end Perennial
