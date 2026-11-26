/-
`crc32.archAvailableCastagnoli()` (`crc32_amd64.go`; the Go model `models/hash/crc32/model.go`, until 2026-11-24 the trusted `TrustedCode/hash/crc32.lean`):
some `bool`. Lean-first (crc32-hooks2, 2026-11-22).
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
abbrev hash.crc32.archAvailableCastagnoli.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! hash.crc32.archAvailableCastagnoli)) (Val #()))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
