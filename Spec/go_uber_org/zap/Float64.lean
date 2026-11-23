/-
`zap.Float64`: proved over zap's code (2026-11-22, prove-ps2-rqb; `math.Float64bits`, translated in
Perennial). Lean-first (no Rocq counterpart).
-/
module

public import GeneratedProof.go_uber_org.zap
public import Proof.go_uber_org.zap.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_uber_org

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `zap.Float64(...)` returns some field. -/
abbrev zap.Float64.spec : Prop :=
  ∀ (k : GoString) (v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap }}
    (App (App (Val (@! zap.Float64)) (Val #k)) (Val #v))
  {{ (f : zap.zapcore.Field), RET #f; True }}

end spec

end EtcdGrove
end Perennial
