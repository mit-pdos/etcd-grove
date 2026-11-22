/-
prometheus's `Register(c)` (item 4, the server start: `getServerMetrics` registers grpc-prometheus's
server metrics with the default registry). (prom-registry, 2026-11-22) Over the default registry's
model (the trusted glue's `Register`, `TrustedCode/github_com/prometheus/client_golang/prometheus.lean`):
until then a trust-boundary axiom whose post was `True`.
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.PkgInit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lib

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `prometheus.Register(c)` of a collector `c` describing the descriptors `ds` (`collectorDescsAre`:
what its constructor's spec says), all accepted (`descsOk`: valid, each ID its name's, no builtin's
name, one dim hash per name), given the rights to the IDs it registers (`idToks (descKeys ds)`,
consumed: they are registered) and prometheus's initialization, returns `nil`. -/
abbrev prometheus.Register.spec : Prop :=
  ∀ (c : GoInterfaceOk) (ds : List promreg.Desc),
  prometheus.collectorDescsAre c ds → promreg.descsOk prometheus.descId ds →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus ∗
      promreg.idToks (GF := GF) (promreg.descKeys ds) }}
    (App (Val (@! github_com.prometheus.client_golang.prometheus.Register)) (Val #(GoInterface.ok c)))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
