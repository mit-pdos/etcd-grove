/-
`promreg.NewRegistry()` (`promreg.go`): a new, empty registry. Lean-first; see `Proof/github_com/mit_pdos/etcd_grove/examples/lib/promreg/Defs.lean` and
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
variable [promG : promreg.PromRegGS GF]

/-- `NewRegistry()` returns an empty registry, its invariant established (no ID registered, so no
right taken), for any naming `f`. -/
abbrev promreg.NewRegistry.spec : Prop :=
  ∀ (f : GoString → w64),
  {{ (True : IProp GF) }}
    (App (Val (@! promreg.NewRegistry)) (Val #()))
  {{ (r : Loc), RET #r; promreg.isRegistry f r }}

end spec

end EtcdGrove
end Perennial
