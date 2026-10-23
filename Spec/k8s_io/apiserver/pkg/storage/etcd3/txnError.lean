/-
`txnError(succeeded, err)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go`): the error a metric records
(`err`, or `metrics.ErrTransactionConflict` for a failed comparison); some error. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev txnError.spec : Prop :=
  ∀ (succeeded : Bool) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 }}
    (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.txnError)) (Val #succeeded)) (Val #err))
  {{ (e : GoInterface), RET #e; True }}

end spec

end k8s
end EtcdGrove
end Perennial
