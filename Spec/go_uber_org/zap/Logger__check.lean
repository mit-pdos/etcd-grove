/-
`zap.Logger.check` (unexported), proved over zap's code since zap-z1 (2026-11-23,
`Proof/go_uber_org/zap/Logger__check.lean`); until then the trust boundary of zap's leveled logging.
Lean-first. Until 2026-11-20 the boundary was the five exported methods that call it, `Check`
(`return log.check(lvl, msg)`) and `Debug`/`Info`/`Warn`/`Error` (`if ce := log.check(lvl, msg); ce != nil {
ce.Write(fields...) }`, zap v1.28.0 `logger.go:221-265`), each an axiom; this spec is `Check`'s former one,
moved down unchanged, and the five are proved from it (and from `zapcore.CheckedEntry.Write`).
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

/-- `l.check(lvl, msg)` (a zap logger, `zapLoggerOk l`; premise fixes 6: a zero `&zap.Logger{}` panics) at a level below `DPanicLevel` returns a
`*zapcore.CheckedEntry`: `nil` if the level is not enabled, else an entry to write
(`zapcore.zapEntry`, which `CheckedEntry.Write` consumes; logging has no effect here).

(Sweep repairs 1, R1-2, 2026-11-07; the Scope's L1, etcd-grove-82's review blocker 2) The level is a
`zapcore.Level`, an `int8`: `lvl = #(w : w8)` with `sint.Z w < 3`, i.e. `DebugLevel` (`-1`, which
is `255` unsigned) through `ErrorLevel` (`2`). Until then any level was admitted, and an entry at
`PanicLevel` (on any logger, `zap.NewNop()` included) or at `DPanicLevel` under `Development()`
panics in its `Write` (`zapcore/entry.go`; Go: `examples/sweeprepairs/zapcheck`). Its callers in zap: `Check` (whose only
caller, `auth/store.go:358`, checks `DebugLevel`) and `Debug`/`Info`/`Warn`/`Error` (`DebugLevel`
through `ErrorLevel`). -/
abbrev zap.Logger.check.spec : Prop :=
  ∀ (l : Loc) (lvl : val) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ zapLoggerOk l ∗
      ⌜∃ w : w8, lvl = #w ∧ sint.Z w < 3⌝ }}
    (App (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"check")) (Val lvl)) (Val #msg))
  {{ (ce : Loc), RET #ce; ⌜ce = null⌝ ∨ zapcore.zapEntry ce }}

end spec

end EtcdGrove
end Perennial
