/-
`zap.Error`: the trust boundary (`go.uber.org/zap` is names-only). Lean-first (no Rocq counterpart).
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

/-- `zap.Error(...)` returns some field. -/
abbrev zap.Error.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap }}
    (App (Val (@! zap.Error)) (Val #err))
  {{ (f : zap.zapcore.Field), RET #f; True }}

end spec

end EtcdGrove
end Perennial
