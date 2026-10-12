/-
`UnsafeCreateBucket` (the backend). `t.UnsafeCreateBucket(bucket)` under the lock (a name of `1..MaxKeySize` bytes): the bucket,
empty if it was absent.
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `t.UnsafeCreateBucket(bucket)` under the lock (a name of `1..MaxKeySize` bytes): the bucket,
empty if it was absent. -/
abbrev backend.batchTxBuffered.UnsafeCreateBucket.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (WR : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface) (bi : BucketInfo),
  P.has bi → 0 < bi.name.length → bi.name.length ≤ maxKeySize → sint.Z st.pend + 1 < 2 ^ 58 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P WR b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafeCreateBucket")) (Val #bk))
  {{ RET #(); batchLocked γ P b (st.create bi) }}

end spec

end EtcdGrove
end Perennial
