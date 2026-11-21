/-
`d.Write(p)` of a digest over a Castagnoli table (`crc32.go:223-228`: `d.crc = update(d.crc, d.tab, p,
false)`): the digest's checksum extended by `p`'s bytes (`crc32c`), which are only read; it returns
`len(p)` and no error. Lean-first (prove-etcdint3, 2026-11-21).
-/
module

public import Spec.hash.crc32.update

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
abbrev hash.crc32.digest.Write.spec : Prop :=
  ∀ (d : Loc) (c : w32) (tab : Loc) (s : GoSlice) (bs : List w8) (dq : DFrac),
  {{ (d ↦ _root_.Perennial.hash.crc32.digest.mk c tab : IProp GF) ∗ tab ↦□ hash.crc32.castagnoliTableArr ∗
      s ↦*{dq} bs }}
    (App (Val (d @!! go.GoType.PointerType _root_.Perennial.hash.crc32.digest.ty @!! go!"Write"))
      (Val #s))
  {{ RET (PairV #s.len #GoInterface.nil);
      d ↦ _root_.Perennial.hash.crc32.digest.mk (hash.crc32.crc32c c bs) tab ∗ s ↦*{dq} bs }}

end spec

end EtcdGrove
end Perennial
