/-
`UnsafeSeqPut` (the backend). `t.UnsafeSeqPut(bucket, key, value)` under the lock: as `UnsafePut`, the key above the
bucket's buffered keys (its `verify` check).
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

/-- `t.UnsafeSeqPut(bucket, key, value)` under the lock: as `UnsafePut`, the key above the
bucket's buffered keys (its `verify` check). -/
abbrev backend.batchTxBuffered.UnsafeSeqPut.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (WR : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface) (bi : BucketInfo) (key value : GoSlice) (kb vb : GoString),
  P.has bi → 0 < kb.length → kb.length ≤ maxKeySize → vb.length ≤ maxValueSize →
  (∀ e ∈ bkOf st.W.bks bi.id, strLt e.1 kb) → sint.Z st.pend + 1 < 2 ^ 58 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P WR b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi ∗ key ↦*□ kb ∗ value ↦*□ vb }}
    (App (App (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafeSeqPut")) (Val #bk)) (Val #key)) (Val #value))
  {{ RET #(); batchLocked γ P b (st.put bi kb vb true) }}

end spec

end EtcdGrove
end Perennial
