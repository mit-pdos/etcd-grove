/-
`UnsafeDeleteForCompaction` (the backend, new in etcd#21982). `t.UnsafeDeleteForCompaction(bucket, key)` under the
lock: bbolt's writer deletes the entry, with no pending delete counted (the `Unlock` does not
commit: the readers see the key until a later commit), in a hook's bucket only (`LateDel.lean`).
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.LateDel

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

/-- `t.UnsafeDeleteForCompaction(bucket, key)` under the lock: bbolt's writer deletes the entry,
one more pending operation, no pending delete (`BSess.delC`: the `Unlock` does not commit, and
the readers see the key until the next commit, whoever makes it). In a hook's bucket (`P.HB`:
reads of it promise nothing), not a hook's own key (`P.hk`). This model has no spec of it in any
other bucket, `Key` included, where the PR calls it: see `LateDel.lean`. -/
abbrev backend.batchTxBuffered.UnsafeDeleteForCompaction.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface) (bi : BucketInfo) (key : GoSlice) (kb : GoString)
    (dk : DFrac),
  P.has bi → sint.Z st.pend + 1 < 2 ^ 58 → P.HB bi.name = true → P.hk bi.name kb = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi ∗ key ↦*{dk} kb }}
    (App (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafeDeleteForCompaction")) (Val #bk)) (Val #key))
  {{ RET #(); batchLocked γ P b (st.delC bi kb) ∗ key ↦*{dk} kb }}

end spec

end EtcdGrove
end Perennial
