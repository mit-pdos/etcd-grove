/-
`crc32.MakeTable(crc32.Castagnoli)` (`hash/crc32`, the part's trusted model,
`LinuxFs/TrustedCode/hash/crc32.lean`): a table holding the Castagnoli table, read-only for good.
Proved in `LinuxFs/Proof/hash/crc32/MakeTable.lean`. Lean-first.
-/
module

public import LinuxFs.GeneratedProof.hash.crc32
public import LinuxFs.Spec.hash.crc32.Model

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
abbrev hash.crc32.MakeTable.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! hash.crc32.MakeTable)) (Val #hash.crc32.castagnoliPoly))
  {{ (tab : Loc), RET #tab; tab ↦□ hash.crc32.castagnoliTableArr }}

end spec

end EtcdGrove
end Perennial
