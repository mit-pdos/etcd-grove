/-
`UnsafeRange` (the backend). `t.UnsafeRange(bucket, key, endKey, limit)` under the lock: the range of bbolt's writer's
contents (it sees the session's writes), as slices valid while bbolt's write transaction is `st.tx` (until the next commit); a
capability to read them under the lock in a state with that transaction (2026-10-12: it was
`st'.C = st.C`, false: a commit that leaves the data unchanged still replaces the
transaction).
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

/-- `t.UnsafeRange(bucket, key, endKey, limit)` under the lock: the range of bbolt's writer's
contents (it sees the session's writes), as slices valid while bbolt's write transaction is `st.tx` (until the next commit); a
capability to read them under the lock in a state with that transaction (2026-10-12: it was
`st'.C = st.C`, false: a commit that leaves the data unchanged still replaces the
transaction). -/
abbrev backend.batchTxBuffered.UnsafeRange.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (WR : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface) (bi : BucketInfo) (key endKey : GoSlice) (kb eb : GoString) (dk de : DFrac) (limit : w64),
  (endKey = slice.nil ↔ eb = []) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P WR b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi ∗ key ↦*{dk} kb ∗
      endKey ↦*{de} eb }}
    (App (App (App (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafeRange")) (Val #bk)) (Val #key)) (Val #endKey)) (Val #limit))
  {{ (keys vals : GoSlice), RET (PairV #keys #vals); batchLocked γ P b st ∗
      key ↦*{dk} kb ∗ endKey ↦*{de} eb ∗
      kvsOutRd st.tx keys vals (cursorRange (bktEnts (bktOf st.S bi.name)) kb eb limit) ∗
      □ (∀ (s : GoSlice) (v : GoString) (st' : BSess), rdB st.tx s v -∗ batchLocked γ P b st' -∗
          ⌜st'.tx = st.tx⌝ -∗
          ∃ dq : DFrac, s ↦*{dq} v ∗ (s ↦*{dq} v -∗ batchLocked γ P b st')) }}

end spec

end EtcdGrove
end Perennial
