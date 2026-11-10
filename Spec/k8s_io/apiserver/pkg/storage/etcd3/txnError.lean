/-
`txnError(succeeded, err)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go:1322-1330`): the error a
metric records (`err`, or `metrics.ErrTransactionConflict` for a failed comparison, or `nil`): one
grpc's `status` accepts (`statusErrOk`) if `err` is, which `metrics.RecordEtcdRequest` needs
(premise fixes 3, 2026-11-10: it was some error; `ErrTransactionConflict` is an `errors.New` leaf,
`metricsInit`). Lean-first (no Rocq counterpart).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev txnError.spec : Prop :=
  ∀ (succeeded : Bool) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 }}
    (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.txnError)) (Val #succeeded)) (Val #err))
  {{ (e : GoInterface), RET #e;
      go_etcd_io.etcd.cache.v3.statusErrOk err -∗ go_etcd_io.etcd.cache.v3.statusErrOk e }}

end spec

end k8s
end EtcdGrove
end Perennial
