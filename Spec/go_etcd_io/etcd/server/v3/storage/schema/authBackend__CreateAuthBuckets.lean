/-
`(*authBackend).CreateAuthBuckets()` (`auth.go`): the three auth buckets created in one batch
session (`LockOutsideApply`, three `UnsafeCreateBucket`s, the deferred `Unlock`).
Lean-first (no Rocq counterpart); the authstore-noax stage (2026-11-18, `notes/decisions.md`,
"authstore-noax").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBackendReal
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__BatchTx
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__LockOutsideApply
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Unlock

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- An `authBackend` over the real backend `b`, with the three auth buckets in its table and tracked,
and the client's part of a set `S` of tracked buckets holding them, at `r`: one write-back token
spent (the `Unlock`), the part given back **idle** at the buckets present (`authCreated r`: each
`∅` if it was absent; an existing bucket kept, bbolt's `CreateBucketIfNotExists`). -/
abbrev schema.authBackend.CreateAuthBuckets.spec : Prop :=
  ∀ (abe : Loc) (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (qo : Qp)
    (S : GoString → Prop) (r : GMap GoString BktData),
  (∀ bi ∈ [mvcc.authBI, mvcc.authUsersBI, mvcc.authRolesBI], P.has bi ∧ P.RB bi.name = true ∧
    S bi.name) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      schema.abeF go!"be" abe ↦□ (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b : GoInterface) ∗
      isBackend γ P W Pk b ∗ bOpen γ qo ∗ wbTok γ ∗ rbPart γ S r }}
    (App (Val (abe @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty @!! go!"CreateAuthBuckets"))
      (Val #()))
  {{ RET #(); bOpen γ qo ∗ rbOwnIn γ S (schema.authCreated r) }}

end spec

end EtcdGrove
end Perennial
