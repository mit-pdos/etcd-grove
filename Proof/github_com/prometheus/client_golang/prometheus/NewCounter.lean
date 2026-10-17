/-
Trust boundary: prometheus's `NewCounter` (an axiom; see
`Spec/github_com/prometheus/client_golang/prometheus/NewCounter.lean`).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.NewCounter

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (item 8, the read package's initializer). True of prometheus's Go code
(client_golang v1.24.1, `counter.go`): `NewCounter(opts)` makes the descriptor
`V2.NewDesc(BuildFQName(ns, sub, name), help, nil, opts.ConstLabels, WithUnit(opts.Unit))`, which
records an error rather than panicking (here none: the name is non-empty ASCII, valid UTF-8, and
there are no labels), sets `now = time.Now`, and returns a `*counter` (its `Describe` sends that
one descriptor) without panicking. Its `Inc` adds 1 and its `Add(v)` panics only if `v < 0`
(`counter.go`: "counter cannot decrease in value"), which `counterSpec` excludes. -/
axiom prometheus.NewCounter.wp_proof : prometheus.NewCounter.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
