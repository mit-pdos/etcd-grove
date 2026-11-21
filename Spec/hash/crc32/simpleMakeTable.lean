/-
`crc32.simpleMakeTable(poly)` (`crc32_generic.go:20-24`): a fresh table holding `poly`'s
(`crcTableOf poly`). Lean-first (prove-etcdint3, 2026-11-21).
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
abbrev hash.crc32.simpleMakeTable.spec : Prop :=
  ∀ (poly : w32),
  {{ (True : IProp GF) }}
    (App (Val (@! hash.crc32.simpleMakeTable)) (Val #poly))
  {{ (t : Loc), RET #t; t ↦ (array.mk 256 (hash.crc32.crcTableOf poly) : GoArray w32 256) }}

end spec

end EtcdGrove
end Perennial
