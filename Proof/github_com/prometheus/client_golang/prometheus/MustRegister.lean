/-
Trust boundary: prometheus's `MustRegister` (an axiom; see
`Spec/github_com/prometheus/client_golang/prometheus/MustRegister.lean`).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.MustRegister

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
(client_golang v1.24.1, `registry.go`): `MustRegister(cs...)` is
`DefaultRegisterer.MustRegister(cs...)` (etcd never reassigns `DefaultRegisterer`, the
`*Registry` `defaultRegistry`), which panics only if `Registry.Register(c)` returns an error.
`Register` (under the registry's mutex) fails only if a descriptor `c` describes has an error,
or its ID is registered, or a registered descriptor has its name with other labels or help, or
`c`'s collector ID (the XOR of its descriptor IDs) is registered. Here `c` describes one valid
descriptor named `n` without labels (`collectorName`), so its collector ID is that descriptor's
ID, and `nameFree n` says no registered descriptor is named `n` or has that ID, and no collector
has it: `Register` registers `c` and returns `nil`. The slice is only read. -/
axiom prometheus.MustRegister.wp_proof : prometheus.MustRegister.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
