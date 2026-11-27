/-
`encodeMetadataHeader(k, v)` (the grpc model's `model_http_util.go`, grpc-go's `http_util.go`): the
field value a metadata pair is written as.
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

/-- `encodeMetadataHeader(k, v)` returns `encMdHdr k v`: `b64Raw v` for a `-bin` key, `v`
otherwise. -/
abbrev grpc.encodeMetadataHeader.spec : Prop :=
  ∀ (k v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (App (Val (@! google_golang_org.grpc.encodeMetadataHeader)) (Val #k)) (Val #v))
  {{ RET #(grpcHdr.encMdHdr k v); True }}

end spec

end EtcdGrove
end Perennial
