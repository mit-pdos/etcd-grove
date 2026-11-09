/-
`(*zapcore.CheckedEntry).Write`: the trust boundary.
Users: `server/auth/store.go` (`Check(DebugLevel, ...)` then `Write`).
Proof sketch: none (trust boundary, `../Api.lean`'s header).
Changes: from `specs-ref/Spec/go_uber_org/zap/zapcore/CheckedEntry__Write.lean`: `entryOk` for
`zapEntry`, the namespace `Zap`.
Margin: logging's output is not modelled.
-/
module

public import Spec.go_uber_org.zap.Api
public import Spec.PkgInit.go_uber_org.zap.zapcore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Zap

open Iris Iris.BI go_uber_org

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `ce.Write(fields...)` of an entry `Check` returned, not yet written (consumed), returns. -/
def zapcore.CheckedEntry.Write.spec : Prop :=
  ∀ (ce : Loc) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap.zapcore ∗ entryOk ce }}
    (App (Val (ce @!! go.GoType.PointerType zap.zapcore.CheckedEntry.ty @!! go!"Write")) (Val #fields))
  {{ RET #(); True }}

end spec

end Zap
end EtcdGrove
end Perennial
