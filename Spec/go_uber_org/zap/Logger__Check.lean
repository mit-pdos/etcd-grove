/-
`zap.Logger.Check`: the trust boundary (`go.uber.org/zap` is names-only). Lean-first (no Rocq
counterpart); the auth plan's S5 (2026-10-24: `auth.authStore.Authenticate` logs through it).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import GeneratedProof.go_uber_org.zap
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

/-- `l.Check(lvl, msg)` (a non-nil logger) at a level below `DPanicLevel` returns a
`*zapcore.CheckedEntry`: `nil` if the level is not enabled, else an entry to write
(`zapcore.zapEntry`, which `CheckedEntry.Write` consumes; logging has no effect here).

(Sweep repairs 1, R1-2, 2026-11-07; the Scope's L1, etcd-grove-82's review blocker 2) The level is a
`zapcore.Level`, an `int8`: `lvl = #(w : w8)` with `sint.Z w < 3`, i.e. `DebugLevel` (`-1`, which
is `255` unsigned) through `ErrorLevel` (`2`). Until then any level was admitted, and an entry at
`PanicLevel` (on any logger, `zap.NewNop()` included) or at `DPanicLevel` under `Development()`
panics in its `Write` (`zapcore/entry.go`; Go: `examples/sweeprepairs/zapcheck`). Its only caller,
`auth/store.go:358`, checks `DebugLevel`. (The logger's premise is still `l ≠ null` until sweep
repairs 1's LG-5, which asks `zapLoggerOk l`.) -/
abbrev zap.Logger.Check.spec : Prop :=
  ∀ (l : Loc) (lvl : val) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ ⌜l ≠ null⌝ ∗
      ⌜∃ w : w8, lvl = #w ∧ sint.Z w < 3⌝ }}
    (App (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"Check")) (Val lvl)) (Val #msg))
  {{ (ce : Loc), RET #ce; ⌜ce = null⌝ ∨ zapcore.zapEntry ce }}

end spec

end EtcdGrove
end Perennial
