/-
`crc32.Update(crc, tab, p)` with `tab` a Castagnoli table (`hash/crc32`, the part's trusted model,
`LinuxFs/TrustedCode/hash/crc32.lean`): `crc32c crc p`; `p` is only read, at any fraction, and the
table is read-only for good. Proved in `LinuxFs/Proof/hash/crc32/Update.lean`. Lean-first.
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
abbrev hash.crc32.Update.spec : Prop :=
  ∀ (c : w32) (tab : Loc) (s : GoSlice) (bs : List w8) (dq : DFrac),
  {{ (tab ↦□ hash.crc32.castagnoliTableArr : IProp GF) ∗ s ↦*{dq} bs }}
    (App (App (App (Val (@! hash.crc32.Update)) (Val #c)) (Val #tab)) (Val #s))
  {{ RET #(hash.crc32.crc32c c bs); s ↦*{dq} bs }}

end spec

end EtcdGrove
end Perennial
