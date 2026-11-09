/-
`zap.Binary`: the trust boundary.
Users: mvcc (`kvstore_txn.go:135`).
Proof sketch: none (trust boundary, `Api.lean`'s header).
Changes: new (verify round, A1-completeness S1: a specced caller uses it and no spec existed).
Margin: logging's output is not modelled; the field keeps the slice, which the logger reads when it encodes the entry (synchronously, in the logging call: zap's cores copy nothing later), so the caller needs no ownership beyond the call.
-/
module

public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Zap

open Iris Iris.BI go_uber_org

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `zap.Binary(key, b)` returns a field (a plain value keeping the slice). -/
def Binary.spec : Prop :=
  ∀ (k : GoString) (b : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap }}
    (App (App (Val (@! zap.Binary)) (Val #k)) (Val #b))
  {{ (f : zap.zapcore.Field), RET #f; True }}

end spec

end Zap
end EtcdGrove
end Perennial
