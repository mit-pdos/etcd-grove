/-
`encodeBinHeader(v)` (the grpc model's `model_http_util.go`, grpc-go's `http_util.go`): a `-bin`
header's value, `base64.RawStdEncoding.EncodeToString(v)`.
-/
module

public import Proof.google_golang_org.grpc.HeaderFields

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

/-- `encodeBinHeader(v)` returns `b64Raw` of `v`'s bytes, reading and keeping the slice. -/
abbrev grpc.encodeBinHeader.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (d : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ sl ↦*{dq} d }}
    (App (Val (@! google_golang_org.grpc.encodeBinHeader)) (Val #sl))
  {{ RET #(b64Raw d); sl ↦*{dq} d }}

end spec

end EtcdGrove
end Perennial
