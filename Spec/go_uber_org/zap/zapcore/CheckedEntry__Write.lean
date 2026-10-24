/-
`zapcore.CheckedEntry.Write`: the trust boundary (`go.uber.org/zap/zapcore` is names-only).
Lean-first (no Rocq counterpart); the auth plan's S5 (2026-10-24: `auth.authStore.Authenticate`
writes the entry `zap.Logger.Check` returned).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import GeneratedProof.go_uber_org.zap.zapcore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_uber_org

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `ce.Write(fields...)` (a non-nil entry, as `Check` returned it) returns: logging has no effect
here. -/
abbrev zapcore.CheckedEntry.Write.spec : Prop :=
  ∀ (ce : Loc) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap.zapcore ∗ ⌜ce ≠ null⌝ }}
    (App (Val (ce @!! go.GoType.PointerType zap.zapcore.CheckedEntry.ty @!! go!"Write")) (Val #fields))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
