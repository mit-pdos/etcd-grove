/-
`audit.GetAuditIDTruncated(ctx)` (names-only): some string. The trust boundary: an axiom, `Proof/k8s_io/apiserver/pkg/audit/GetAuditIDTruncated.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev audit.GetAuditIDTruncated.spec : Prop :=
  ∀ (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.audit }}
    (App (Val (@! k8s_io.apiserver.pkg.audit.GetAuditIDTruncated)) (Val #ctx))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
