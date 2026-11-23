/-
`crc32.archInitCastagnoli()` (`crc32_amd64.go`; trusted model, `TrustedCode/hash/crc32.lean`): returns.
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
abbrev hash.crc32.archInitCastagnoli.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! hash.crc32.archInitCastagnoli)) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
