/-
`zap.Logger.Panic`: the trust boundary (`go.uber.org/zap` is names-only). Lean-first (no Rocq counterpart).
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

/-- `l.Panic(msg, fields...)` (a non-nil logger) logs, then panics with the message (zapcore's
`CheckedEntry.Write`: `panic(ce.Message)`), whatever the logger's core (a nop logger too:
`Panic`/`Fatal` entries are always written). -/
abbrev zap.Logger.Panic.spec : Prop :=
  ∀ (l : Loc) (msg : GoString) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ ⌜l ≠ null⌝ }}
    (App (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"Panic")) (Val #msg)) (Val #fields))
  {{ (r : val), RET r; ⌜r = PanicV #msg⌝ }}

end spec

end EtcdGrove
end Perennial
