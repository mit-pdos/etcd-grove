/-
`attribute.NewEncoderID` (`encoder.go:76`, `EncoderID{value: encoderIDCounter.Add(1)}`), for the
package's own `init` (the fork's `id := NewEncoderID(); defaultEncoderID = id`, which sets
`defaultEncoderID`: etc/goose.py's `module_forks`). Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.sync.atomic.Base
public import GeneratedProof.go_opentelemetry_io.otel.«attribute»

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_opentelemetry_io.otel.«attribute».Assumptions]

/-- `NewEncoderID()`, given the counter `encoderIDCounter` at `n` (an `atomic.Uint64`, owned: the
package's `init` calls it before any other code can): it returns the ID `n + 1` and leaves the
counter at `n + 1`. (No `isPkgInit` of `attribute`: its `init` calls it.) -/
abbrev «attribute».NewEncoderID.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗
      sync.atomic.ownUint64 (globalAddr go_opentelemetry_io.otel.«attribute».encoderIDCounter)
        (DFrac.own 1) n }}
    (App (Val (@! go_opentelemetry_io.otel.«attribute».NewEncoderID)) (Val #()))
  {{ RET #(({ value' := n + 1 } : go_opentelemetry_io.otel.«attribute».EncoderID));
      sync.atomic.ownUint64 (globalAddr go_opentelemetry_io.otel.«attribute».encoderIDCounter)
        (DFrac.own 1) (n + 1) }}

end spec

end EtcdGrove
end Perennial
