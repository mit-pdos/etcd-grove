/-
## `attribute.Bool(k, v)`: assumed

**Users.** The server's span attributes (`etcdserver/v3_server.go`). **Assumed**: a struct literal
(otel's `attribute/kv.go`), total.
-/
module

public import SpecPlan.Spec.go_opentelemetry_io.otel.attribute.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace OtelAttribute

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_opentelemetry_io.otel.«attribute».Assumptions]

/-- `attribute.Bool(k, v)` returns a key-value. -/
def Bool.spec : Prop :=
  ∀ (k : GoString) (v : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.«attribute» }}
    (App (App (Val (@! go_opentelemetry_io.otel.«attribute».Bool')) (Val #k)) (Val #v))
  {{ (r : val), RET r; True }}

end spec
end OtelAttribute
end EtcdGrove
end Perennial
