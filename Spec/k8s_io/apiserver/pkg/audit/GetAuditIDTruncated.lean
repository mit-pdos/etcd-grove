/-
`audit.GetAuditIDTruncated(ctx)` (names-only): some string. It reads `ctx.Value(auditKey)`
(`AuditContextFrom`), so `ctx` is not nil and its `Value` at that key returns (premise-fixes-7; a
nil or misbehaving context panics, `examples/premisefix/k8sctx`). The trust boundary: an axiom, `Proof/k8s_io/apiserver/pkg/audit/GetAuditIDTruncated.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.k8s_io.apiserver.pkg.audit.CtxKeys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev audit.GetAuditIDTruncated.spec : Prop :=
  ∀ (ctx : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.audit ∗
      context.valueAt ctx audit.auditKeyAny (fun _ => True) }}
    (App (Val (@! k8s_io.apiserver.pkg.audit.GetAuditIDTruncated)) (Val #(GoInterface.ok ctx)))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
