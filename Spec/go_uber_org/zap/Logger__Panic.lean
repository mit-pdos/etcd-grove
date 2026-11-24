/-
`zap.Logger.Panic`: proved over zap's code (`Proof/go_uber_org/zap/Logger__Panic.lean`; zap-z2, 2026-11-23:
until then the trust boundary). Lean-first (no Rocq counterpart).
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

/-- `l.Panic(msg, fields...)` (a zap logger, `zapLoggerOk l`) logs, then panics with the message as an
`any` (zapcore's `CheckedEntry.Write`: `panic(ce.Message)`), whatever the logger's core (a nop logger
too: `Panic`/`Fatal` entries are always written). The premise is `zapLoggerOk l`, not `l ≠ null`
(2026-11-17, `notes/specs-only/ledger.md`): a zero `&zap.Logger{}` panics with a nil-dereference
runtime error instead of the message, and a logger with a custom `WithPanicHook` that returns makes
`Panic` return. -/
abbrev zap.Logger.Panic.spec : Prop :=
  ∀ (l : Loc) (msg : GoString) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ zapLoggerOk l }}
    (App (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"Panic")) (Val #msg)) (Val #fields))
  {{ (r : val), RET r; ⌜r = PanicV #(interface.mkOk go.string #msg)⌝ }}

end spec

end EtcdGrove
end Perennial
