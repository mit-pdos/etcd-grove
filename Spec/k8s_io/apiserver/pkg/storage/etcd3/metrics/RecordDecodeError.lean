/-
`metrics.RecordDecodeError(gr)` (names-only): a no-op for the store's results. The trust boundary: an axiom, `Proof/k8s_io/apiserver/pkg/storage/etcd3/metrics/RecordDecodeError.lean`. Lean-first (no Rocq
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
abbrev metrics.RecordDecodeError.spec : Prop :=
  ∀ (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordDecodeError)) (Val #gr))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
