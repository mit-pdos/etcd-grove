/-
`crc32.slicingMakeTable(poly)` (`crc32_generic.go:60-72`): a fresh slicing-by-8 table holding
`poly`'s (`slicingTableArr poly`: table `j`, entry `i` is `8 (j + 1)` reflected steps from `i`).
Lean-first (crc32-hooks2, 2026-11-22).
-/
module

public import GeneratedProof.hash.crc32
public import Spec.hash.crc32.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [hash.crc32.Assumptions]

/-- See the file header. -/
abbrev hash.crc32.slicingMakeTable.spec : Prop :=
  ∀ (poly : w32),
  {{ (True : IProp GF) }}
    (App (Val (@! hash.crc32.slicingMakeTable)) (Val #poly))
  {{ (t : Loc), RET #t; t ↦ hash.crc32.slicingTableArr poly }}

end spec

end EtcdGrove
end Perennial
