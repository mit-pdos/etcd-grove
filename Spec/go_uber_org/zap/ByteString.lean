/-
`zap.ByteString`: the trust boundary (`go.uber.org/zap` is names-only). Lean-first (no Rocq
counterpart; unit P2: the auth store's `isOpPermitted` logs the key).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `zap.ByteString(key, val)` returns some field (it keeps the slice, reading it only when the
entry is encoded). -/
abbrev zap.ByteString.spec : Prop :=
  ∀ (k : GoString) (v : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap }}
    (App (App (Val (@! zap.ByteString)) (Val #k)) (Val #v))
  {{ (f : zap.zapcore.Field), RET #f; True }}

end spec

end EtcdGrove
end Perennial
