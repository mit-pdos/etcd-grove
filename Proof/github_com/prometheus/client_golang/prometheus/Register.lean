/-
Trust boundary: prometheus's `Register` (an axiom; see `Spec/github_com/prometheus/client_golang/prometheus/Register.lean`).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.Register

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (item 4, the server start): `Register` registers the collector with the
default registry (under its mutex): it calls `m.Describe` (the metrics' descriptors, sent on a
channel the registry drains) and checks them against the registered ones, returning an error on a
conflict (e.g. registered twice). -/
axiom prometheus.Register.wp_proof : prometheus.Register.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
