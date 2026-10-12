/-
`trace.WithAttributes`: the trust boundary (`go.opentelemetry.io/otel/trace` is names-only). Lean-first (no Rocq counterpart); the request path
(`notes/decisions.md`, "The request path").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `trace.WithAttributes(kvs...)`: a span start option (the attributes of a trace span: no
effect the model sees); it returns. -/
abbrev trace.WithAttributes.spec : Prop :=
  ∀ (kvs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.trace }}
    (App (Val (@! go_opentelemetry_io.otel.trace.WithAttributes)) (Val #kvs))
  {{ (o : GoInterface), RET #o; True }}

end spec

end EtcdGrove
end Perennial
