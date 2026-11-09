/-
## `trace.WithAttributes(attrs...)`: assumed

**Users.** The server's spans (`v3_server.go`, `Tracer.Start`'s options). **Assumed**: otel's
`trace/config.go` wraps the slice in an `attributeOption` (no copy, no check), total.
-/
module

public import Spec.go_opentelemetry_io.otel.trace.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace OtelTrace

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_opentelemetry_io.otel.trace.Assumptions]

/-- `trace.WithAttributes(attrs...)` returns an option. -/
def WithAttributes.spec : Prop :=
  ∀ (attrs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.trace }}
    (App (Val (@! go_opentelemetry_io.otel.trace.WithAttributes)) (Val #attrs))
  {{ (o : GoInterface), RET #o; True }}

end spec
end OtelTrace
end EtcdGrove
end Perennial
