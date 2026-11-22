/-
`crc32.simpleUpdate(crc, tab, p)` (`crc32_generic.go:44-50`): the table-driven CRC of `p` over the
table `tab` holds (`crcUpdate`), which it only reads. Lean-first (crc32-hooks2, 2026-11-22).
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
abbrev hash.crc32.simpleUpdate.spec : Prop :=
  ∀ (c : w32) (tab : Loc) (dt : DFrac) (a : GoArray w32 256) (s : GoSlice) (bs : List w8) (dq : DFrac),
  {{ (tab ↦{dt} a : IProp GF) ∗ s ↦*{dq} bs }}
    (App (App (App (Val (@! hash.crc32.simpleUpdate)) (Val #c)) (Val #tab)) (Val #s))
  {{ RET #(hash.crc32.crcUpdate a.arr c bs); tab ↦{dt} a ∗ s ↦*{dq} bs }}

end spec

end EtcdGrove
end Perennial
