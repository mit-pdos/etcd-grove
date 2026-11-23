/-
`crc32.slicingUpdate(crc, tab, p)` (`crc32_generic.go:76-93`) over `poly`'s slicing-by-8 table: the
same CRC as `simpleUpdate` over `poly`'s simple table (`crcUpdate (crcTableOf poly)`), eight bytes a
round while more than eight remain (once `p` has at least 16), the rest by `simpleUpdate` of table
`0`. Lean-first (crc32-hooks2, 2026-11-22).
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
abbrev hash.crc32.slicingUpdate.spec : Prop :=
  ∀ (poly c : w32) (tab : Loc) (s : GoSlice) (bs : List w8) (dq : DFrac),
  {{ (tab ↦□ hash.crc32.slicingTableArr poly : IProp GF) ∗ s ↦*{dq} bs }}
    (App (App (App (Val (@! hash.crc32.slicingUpdate)) (Val #c)) (Val #tab)) (Val #s))
  {{ RET #(hash.crc32.crcUpdate (hash.crc32.crcTableOf poly) c bs); s ↦*{dq} bs }}

end spec

end EtcdGrove
end Perennial
