/-
`zap.SugaredLogger.Infof`: the trust boundary (`go.uber.org/zap` is names-only). Lean-first (no
Rocq counterpart); the watch slice's unit W-S (2026-10-14: `recvLoop`'s log of an invalid request).
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

/-- `sl.Infof(template, args...)` (a non-nil sugared logger) returns: logging has no effect
here. -/
abbrev zap.SugaredLogger.Infof.spec : Prop :=
  ∀ (sl : Loc) (tmpl : GoString) (args : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ ⌜sl ≠ null⌝ }}
    (App (App (Val (sl @!! go.GoType.PointerType zap.SugaredLogger.ty @!! go!"Infof")) (Val #tmpl))
      (Val #args))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
