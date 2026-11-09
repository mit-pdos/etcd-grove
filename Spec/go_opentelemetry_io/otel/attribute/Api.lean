/-
# OpenTelemetry's `attribute` package: the trust boundary (batch 4b)

Translated types and names only: **assumed**. etcd builds span attributes (`attribute.String`,
`Int64`, `Int`, `Bool`) only to pass them to `trace.WithAttributes` (`OtelTrace`); each constructor
is total (otel's `attribute/kv.go`: a struct literal of the key and an `attribute.Value`, no check).
No vocabulary: a `KeyValue` is a plain value.
-/
module

public import GeneratedProof.go_opentelemetry_io.otel.attribute
public import Spec.PkgInit.go_opentelemetry_io.otel.attribute

@[expose] public section
