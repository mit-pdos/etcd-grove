/-
`crc32.archUpdateCastagnoli(crc, p)` (`crc32_amd64.go`; trusted model, `TrustedCode/hash/crc32.lean`):
the CRC-32C of `p` from `crc`, reading `p`. Lean-first (crc32-hooks2, 2026-11-22).
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
abbrev hash.crc32.archUpdateCastagnoli.spec : Prop :=
  ∀ (c : w32) (s : GoSlice) (bs : List w8) (dq : DFrac),
  {{ (s ↦*{dq} bs : IProp GF) }}
    (App (App (Val (@! hash.crc32.archUpdateCastagnoli)) (Val #c)) (Val #s))
  {{ RET #(hash.crc32.crc32c c bs); s ↦*{dq} bs }}

end spec

end EtcdGrove
end Perennial
