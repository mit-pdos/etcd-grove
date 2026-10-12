/-
`zap.Logger.Panic`: the trust boundary (`go.uber.org/zap` is names-only). Lean-first.

`l.Panic(msg, fields...)` logs the message and then panics (zap's `WriteThenPanic`, whatever
the logger's level; a logger built `WithPanicHook` could do otherwise, which etcd's loggers are
not): it never returns. Its outcome is a panic (Perennial's `PanicV`, "Panic and recover" in
`notes/decisions.md`), whose value is left open (zap panics with the message).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import GeneratedProof.go_uber_org.zap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_uber_org

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `l.Panic(msg, fields...)` (a non-nil logger) panics. -/
abbrev zap.Logger.Panic.spec : Prop :=
  ∀ (l : Loc) (msg : GoString) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ ⌜l ≠ null⌝ }}
    (App (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"Panic")) (Val #msg)) (Val #fields))
  {{ (r : val), RET r; ⌜∃ p : val, r = PanicV p⌝ }}

end spec

end EtcdGrove
end Perennial
