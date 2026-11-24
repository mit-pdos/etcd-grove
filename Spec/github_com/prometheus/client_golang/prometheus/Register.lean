/-
prometheus's `Register(c)` (client_golang v1.24.1, `registry.go:167`, translated with its body:
`DefaultRegisterer.Register(c)`; route (b), notes/prom-registry.md): item 4, the server start
(`getServerMetrics` registers grpc-prometheus's server metrics with the default registry). (Until
2026-11-22 names only, a trust-boundary axiom whose post was `True`.)
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.PkgInit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `prometheus.Register(c)` of a collector `c` that describes the descriptors `ps` (`describes`), whose
values are `ds` (`descsOk`: valid, label-free, no built-in name, names and IDs pairwise distinct), given
prometheus's fact and the rights to their keys (`descKeys ds`: the IDs and the collector ID) at the run's
registry name (`PromRegGS`, the fact's parameter; consumed: the registry keeps them), returns nil. -/
abbrev prometheus.Register.spec : Prop :=
  ∀ [promreg_gs : prometheus.PromRegGS GF] (c : GoInterfaceOk) (ps : List Loc)
    (ds : List github_com.prometheus.client_golang.prometheus.Desc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus ∗
      prometheus.describes c ps ∗ ([∗list] p;d ∈ ps;ds, p ↦□ d) ∗
      prometheus.idToks (prometheus.PromRegGS.γ (GF := GF)) (prometheus.descKeys ds) ∗
      ⌜prometheus.descsOk ds⌝ }}
    (App (Val (@! github_com.prometheus.client_golang.prometheus.Register)) (Val #(GoInterface.ok c)))
  {{ RET #(interface.nil : GoInterface); True }}

end spec

end EtcdGrove
end Perennial
