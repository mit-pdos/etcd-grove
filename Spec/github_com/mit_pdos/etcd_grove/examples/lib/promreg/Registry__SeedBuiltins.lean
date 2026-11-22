/-
`(*promreg.Registry).SeedBuiltins()` (`promreg.go`): the builtins registered. Lean-first; see `Proof/github_com/mit_pdos/etcd_grove/examples/lib/promreg/Defs.lean` and
notes/prom-registry.md.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.promreg.Defs

@[expose] public section

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

/-- `r.SeedBuiltins()` registers the builtins, taking their rights (`builtinToks`: prometheus's
initializer's). -/
abbrev promreg.Registry.SeedBuiltins.spec : Prop :=
  ∀ (γ : GName) (f : GoString → w64) (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.promreg ∗ promreg.isRegistry (GF := GF) γ f r ∗ promreg.builtinToks (GF := GF) γ }}
    (App (Val (r @!! go.GoType.PointerType promreg.Registry.ty @!! go!"SeedBuiltins")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
