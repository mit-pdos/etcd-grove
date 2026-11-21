/-
`crc32.simplePopulateTable(poly, t)` (`crc32_generic.go:28-41`): `t` ends holding the table of `poly`
(`crcTableOf poly`: entry `i` is eight reflected shift-xor steps from `uint32(i)`, the trusted model's
definition). Lean-first (prove-etcdint3, 2026-11-21).
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
abbrev hash.crc32.simplePopulateTable.spec : Prop :=
  ∀ (poly : w32) (t : Loc) (a : GoArray w32 256),
  {{ (t ↦ a : IProp GF) }}
    (App (App (Val (@! hash.crc32.simplePopulateTable)) (Val #poly)) (Val #t))
  {{ RET #(); t ↦ (array.mk 256 (hash.crc32.crcTableOf poly) : GoArray w32 256) }}

end spec

end EtcdGrove
end Perennial
