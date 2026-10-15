/-
`attribute.Int`: the trust boundary (`go.opentelemetry.io/otel/attribute` is names-only). Lean-first (no Rocq counterpart); the request path
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
variable [package_sem : go_opentelemetry_io.otel.«attribute».Assumptions]

/-- `attribute.Int(k, v)`: the key-value attribute of the key `k` and an `int` `v` (a span's
attribute: no effect the model sees); it returns. -/
abbrev «attribute».Int.spec : Prop :=
  ∀ (k : GoString) (v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.«attribute» }}
    (App (App (Val (@! go_opentelemetry_io.otel.«attribute».Int')) (Val #k)) (Val #v))
  {{ (kv : go_opentelemetry_io.otel.«attribute».KeyValue), RET #kv; True }}

end spec

end EtcdGrove
end Perennial
