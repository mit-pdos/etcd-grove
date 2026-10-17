/-
`zap.Strings`: the trust boundary (`go.uber.org/zap` is names-only). Lean-first (no Rocq
counterpart; etcd#21764 (pr-verify): the request log's `compare_keys`).
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

/-- `zap.Strings(...)` returns some field (it keeps the slice, which the logger reads when it
encodes the entry; logging has no effect here, as for `zap.ByteString`). -/
abbrev zap.Strings.spec : Prop :=
  ∀ (k : GoString) (v : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap }}
    (App (App (Val (@! zap.Strings)) (Val #k)) (Val #v))
  {{ (f : zap.zapcore.Field), RET #f; True }}

end spec

end EtcdGrove
end Perennial
