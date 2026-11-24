/-
prometheus's `(*Registry).MustRegister` (client_golang v1.24.1, `registry.go:416-422`, translated with
its body; route (b), notes/prom-registry.md) of one collector: it returns, given the rights to the
collector's keys.
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

/-- `r.MustRegister(c)` of one collector `c` describing `ps` (values `ds`, `descsOk`), given the rights
to its keys (consumed), returns (Go panics if `Register` fails: `prometheus.Registry.Register.spec`).
The slice is read at any fraction and kept. -/
abbrev prometheus.Registry.MustRegister.spec : Prop :=
  ∀ (γ : GName) (r : Loc) (s : GoSlice) (dq : DFrac) (c : GoInterfaceOk) (ps : List Loc)
    (ds : List github_com.prometheus.client_golang.prometheus.Desc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ prometheus.isRegistry γ r ∗
      s ↦*{dq} [GoInterface.ok c] ∗
      prometheus.describes c ps ∗ ([∗list] p;d ∈ ps;ds, p ↦□ d) ∗
      prometheus.idToks γ (prometheus.descKeys ds) ∗ ⌜prometheus.descsOk ds⌝ }}
    (App (Val (r @!! go.GoType.PointerType github_com.prometheus.client_golang.prometheus.Registry.ty
      @!! go!"MustRegister")) (Val #s))
  {{ RET #(); s ↦*{dq} [GoInterface.ok c] }}

end spec

end EtcdGrove
end Perennial
