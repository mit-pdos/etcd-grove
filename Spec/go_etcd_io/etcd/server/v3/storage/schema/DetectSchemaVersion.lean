/-
`schema.DetectSchemaVersion(lg, tx)` (`server/storage/schema/schema.go`): the trust boundary
(names-only: `UnsafeReadStorageVersion` parses the stored version with `semver`). Lean-first (etcd
PR #22190's verification, `notes/pr-verify/etcd-22190.md`); see `InvBackendLife.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBackendLife

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- `DetectSchemaVersion(lg, tx)`, with a fraction `O q` of the open token of `tx`'s backend
(`tx.RLock()`, the reads of the `meta` bucket's storage version and consistent index, its
`tx.RUnlock()`): returns some version and error, the fraction given back. -/
abbrev schema.DetectSchemaVersion.spec : Prop :=
  ∀ (lg : Loc) (rt : GoInterfaceOk) (O : Qp → IProp GF) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      schemaReadTx rt O ∗ O q }}
    (App (App (Val (@! schema.DetectSchemaVersion)) (Val #lg)) (Val #(GoInterface.ok rt)))
  {{ (v : github_com.Masterminds.semver.v3.Version) (err : GoInterface), RET (PairV #v #err);
      O q }}

end spec

end EtcdGrove
end Perennial
