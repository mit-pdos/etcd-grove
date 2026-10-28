/-
`UnsafeDelete` (the backend). `t.UnsafeDelete(bucket, key)` under the lock: bbolt's writer deletes the entry; a pending
delete (the `Unlock` commits).
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DelKeys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `t.UnsafeDelete(bucket, key)` under the lock: bbolt's writer deletes the entry; a pending
delete (the `Unlock` commits). Not in a safe-range bucket (`P.SB`), not a hook's own key (`P.hk`);
in a tracked bucket (`P.RB`, D22, 2026-10-23) with the client's half of the tracked buckets
(`rbPut`), given back updated. -/
abbrev backend.batchTxBuffered.UnsafeDelete.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface) (bi : BucketInfo) (key : GoSlice) (kb : GoString)
    (dk : DFrac),
  P.has bi → sint.Z st.pend + 1 < 2 ^ 58 → P.SB bi.name = false → P.hk bi.name kb = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi ∗ key ↦*{dk} kb ∗ rbPut γ P bi.name st.S }}
    (App (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafeDelete")) (Val #bk)) (Val #key))
  {{ RET #(); batchLocked γ P b (st.del bi kb) ∗ key ↦*{dk} kb ∗ rbPut γ P bi.name (st.del bi kb).S }}

/-- **`UnsafeDelete` of any bucket** (the backend-compaction stage, 3.1; Draft, 2026-10-28): of a
safe-range bucket too, for a key registered as deletable at `g` (`dlIs`, decision O1), which the
readers then may miss (3.2). Replaces `spec` once proved (its proof: the batch lemmas over
`safeStC`). -/
abbrev backend.batchTxBuffered.UnsafeDelete.specC : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess)
    (bk : GoInterface) (bi : BucketInfo) (key : GoSlice) (kb : GoString) (dk : DFrac) (own : Bool),
  P.has bi → sint.Z st.pend + 1 < 2 ^ 58 → P.hk bi.name kb = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi ∗
      (if own then key ↦*{dk} kb else txBytes st.tx key kb) ∗
      rbPut γ P bi.name st.S ∗ (if P.SB bi.name then dlIs γ (bi.name, kb) else iprop(True)) }}
    (App (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafeDelete")) (Val #bk)) (Val #key))
  {{ RET #(); batchLocked γ P b (st.del bi kb) ∗
      (if own then key ↦*{dk} kb else txBytes st.tx key kb) ∗ rbPut γ P bi.name (st.del bi kb).S }}

end spec

end EtcdGrove
end Perennial
