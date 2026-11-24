/-
`schema.CreateMetaBucket(tx)` (`server/storage/schema/cindex.go:30-34` at the etcd pin `edc800c6f`).
Lean-first (no Rocq counterpart); claim #34, stage 4 (2026-11-23), for `bootstrapBackend`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.schema

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`CreateMetaBucket(tx)` of the real backend `b`'s batch transaction `t`**, `Meta` in its table
and not a tracked bucket, at an open share and one write-back token: the share comes back. Go:
`tx.LockOutsideApply()`, `tx.UnsafeCreateBucket(Meta)` (bbolt's `CreateBucketIfNotExists`: empty if
absent, else unchanged), the deferred `tx.Unlock()` (a write-back, paid by the token). `Meta` is a
hook's bucket, so the session changes nothing the readers see (`viewSame`). -/
abbrev schema.CreateMetaBucket.spec : Prop :=
  ∀ (γ : backend.BNames) (P : backend.BParams) (W Pk : IProp GF) (b t : Loc) (qo : Qp),
  P.has mvcc.metaBI → P.RB mvcc.metaBI.name = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      backend.isBackend γ P W Pk b ∗ backend.bF go!"batchTx" b ↦□ t ∗ backend.bOpen γ qo ∗
      backend.wbTok γ }}
    (App (Val (@! schema.CreateMetaBucket))
      (Val #(interface.mkOk (go.GoType.PointerType backend.batchTxBuffered.ty) #t)))
  {{ RET #(); backend.bOpen γ qo }}

end spec

end EtcdGrove
end Perennial
