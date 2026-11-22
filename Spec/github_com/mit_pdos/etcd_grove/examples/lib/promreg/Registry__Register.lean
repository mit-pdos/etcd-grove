/-
`(*promreg.Registry).Register(descs)` (`promreg.go`): client_golang's `Register`. Lean-first; see `Proof/github_com/mit_pdos/etcd_grove/examples/lib/promreg/Defs.lean` and
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

/-- `r.Register(descs)` of descriptors the registry accepts (`descsOk`: valid, each ID its name's,
no builtin name, one dim hash per name), given the rights to what they register (`descKeys`: their
IDs and the collector ID), returns `OK` (0): the rights are taken by the registry. -/
abbrev promreg.Registry.Register.spec : Prop :=
  ∀ (γ : GName) (f : GoString → w64) (r : Loc) (s : GoSlice) (dq : DFrac) (ds : List promreg.Desc),
  promreg.descsOk f ds →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.promreg ∗ promreg.isRegistry (GF := GF) γ f r ∗ s ↦*{dq} ds ∗ promreg.idToks (GF := GF) γ (promreg.descKeys ds) }}
    (App (Val (r @!! go.GoType.PointerType promreg.Registry.ty @!! go!"Register")) (Val #s))
  {{ RET #(W64 0); s ↦*{dq} ds }}

end spec

end EtcdGrove
end Perennial
