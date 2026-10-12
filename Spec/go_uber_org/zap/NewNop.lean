/-
`zap.NewNop`: the trust boundary (`go.uber.org/zap` is names-only). Lean-first (no Rocq counterpart).
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

/-- `zap.NewNop()` returns a non-nil logger (one that logs nothing). -/
abbrev zap.NewNop.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap }}
    (App (Val (@! zap.NewNop)) (Val #()))
  {{ (l : Loc), RET #l; ⌜l ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
