/-
prometheus's `(*Registry).Register` (client_golang v1.24.1, `registry.go:283-376`, translated with its
body; route (b), notes/prom-registry.md): registering a collector whose keys the caller holds the rights
to returns nil.
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.RegInv

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

/-- `r.Register(c)` of a collector `c` that describes the descriptors `ps` (`describes`), whose values
are `ds` (`descsOk`: valid, label-free, no built-in name, names and IDs pairwise distinct), given the
rights to their keys (`descKeys ds`: the IDs and the collector ID, consumed: the registry keeps them),
returns nil. (Go returns an error, which `MustRegister` turns into a panic, when a key or a name is
registered already, a descriptor is invalid, or the collector's descriptors disagree.) -/
abbrev prometheus.Registry.Register.spec : Prop :=
  ∀ (γ : GName) (r : Loc) (c : GoInterfaceOk) (ps : List Loc)
    (ds : List github_com.prometheus.client_golang.prometheus.Desc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ prometheus.isRegistry γ r ∗
      prometheus.describes c ps ∗ ([∗list] p;d ∈ ps;ds, p ↦□ d) ∗
      prometheus.idToks γ (prometheus.descKeys ds) ∗ ⌜prometheus.descsOk ds⌝ }}
    (App (Val (r @!! go.GoType.PointerType github_com.prometheus.client_golang.prometheus.Registry.ty
      @!! go!"Register")) (Val #(GoInterface.ok c)))
  {{ RET #(interface.nil : GoInterface); True }}

end spec

end EtcdGrove
end Perennial
