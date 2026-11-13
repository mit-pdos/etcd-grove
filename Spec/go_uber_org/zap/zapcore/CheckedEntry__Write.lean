/-
`zapcore.CheckedEntry.Write`: the trust boundary (`go.uber.org/zap/zapcore` is names-only).
Lean-first (no Rocq counterpart); the auth plan's S5 (2026-10-24: `auth.authStore.Authenticate`
writes the entry `zap.Logger.Check` returned).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import GeneratedProof.go_uber_org.zap.zapcore
public import Spec.go_uber_org.zap.Defs

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

/-- `ce.Write(fields...)` (an entry `Check` returned non-nil, not yet written: `zapcore.zapEntry`,
consumed) returns: logging has no effect here.

(Sweep repairs 1, R1-2, 2026-11-07; the Scope's L1) Until then any non-nil entry was admitted: an
entry at `PanicLevel` (`Check(PanicLevel)` of `zap.NewNop()`) panics in `Write`, as does one at
`DPanicLevel` under `Development()`, a second `Write` of one entry writes to its `ErrorOutput`, and
a hand-built entry may carry any. `Check.spec` gives `zapEntry` only below `DPanicLevel`. -/
abbrev zapcore.CheckedEntry.Write.spec : Prop :=
  ∀ (ce : Loc) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap.zapcore ∗ zapcore.zapEntry ce }}
    (App (Val (ce @!! go.GoType.PointerType zap.zapcore.CheckedEntry.ty @!! go!"Write")) (Val #fields))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
