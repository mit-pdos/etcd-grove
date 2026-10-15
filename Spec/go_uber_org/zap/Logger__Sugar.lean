/-
`zap.Logger.Sugar`: the trust boundary (`go.uber.org/zap` is names-only). Lean-first (no Rocq
counterpart); the watch slice's unit W-S (2026-10-14: `recvLoop`'s log of an invalid request).
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

/-- `l.Sugar()` (a non-nil logger): a non-nil sugared logger. -/
abbrev zap.Logger.Sugar.spec : Prop :=
  ∀ (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ ⌜l ≠ null⌝ }}
    (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"Sugar")) (Val #()))
  {{ (sl : Loc), RET #sl; ⌜sl ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
