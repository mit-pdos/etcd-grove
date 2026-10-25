/-
`zap.Logger.Core`: the trust boundary (`go.uber.org/zap` is names-only). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import GeneratedProof.go_uber_org.zap

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

/-- A `zapcore.Core` interface value: its `Enabled(lvl)` method returns a boolean (persistent). -/
def zap.coreSpec (c : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ (lvl : zap.zapcore.Level),
    {{ True }} (App (Val #(methods c.ty go!"Enabled" c.v)) (Val #lvl)) {{ (b : Bool), RET #b; True }})

instance zap.coreSpec_persistent (c : GoInterfaceOk) :
    Persistent (zap.coreSpec (GF := GF) c) := by
  unfold zap.coreSpec; infer_instance

/-- `l.Core()` on a non-nil `*zap.Logger` returns its `zapcore.Core` (whose `Enabled` returns a
boolean). Note: in Go, `func (log *Logger) Core() zapcore.Core { return log.core }` dereferences
`log` unconditionally, so `l ≠ null` is required. -/
abbrev zap.Logger.Core.spec : Prop :=
  ∀ (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ ⌜l ≠ null⌝ }}
    (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"Core")) (Val #()))
  {{ (c : zap.zapcore.Core), RET #c; ∃ ci : GoInterfaceOk, ⌜c = GoInterface.ok ci⌝ ∗
      zap.coreSpec ci }}

end spec

end EtcdGrove
end Perennial
