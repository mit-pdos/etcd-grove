/-
`zap.String`: the trust boundary (`go.uber.org/zap` is names-only). Lean-first (no Rocq counterpart).
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

/-- `zap.String(...)` returns some field. -/
abbrev zap.String.spec : Prop :=
  ∀ (k : GoString) (v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap }}
    (App (App (Val (@! zap.String)) (Val #k)) (Val #v))
  {{ (f : zap.zapcore.Field), RET #f; True }}

end spec

end EtcdGrove
end Perennial
