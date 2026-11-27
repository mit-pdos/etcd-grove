/-
`appendReset(b, code)` (the grpc model's `model_wire.go`): `b` with a reset frame of the HTTP/2
error code `code` after it (`srvFrameBytes (.reset code)`).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcWire
public import Perennial.Proof.encoding.binary.PtrMethods

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev grpc.appendReset.spec : Prop :=
  ∀ (b : GoSlice) (vs : List w8) (code : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦* vs ∗
      ownSliceCap w8 b (DFrac.own 1) }}
    (App (App (Val (@! google_golang_org.grpc.appendReset)) (Val #b)) (Val #code))
  {{ (r : GoSlice), RET #r; r ↦* (vs ++ srvFrameBytes (.reset (uint.nat code))) ∗
      ownSliceCap w8 r (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
