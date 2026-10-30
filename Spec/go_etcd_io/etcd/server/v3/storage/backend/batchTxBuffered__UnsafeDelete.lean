/-
`UnsafeDelete` (the backend). `t.UnsafeDelete(bucket, key)` under the lock: bbolt's writer deletes the entry; a pending
delete (the `Unlock` commits).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `t.UnsafeDelete(bucket, key)` under the lock: bbolt's writer deletes the entry; a pending
delete (the `Unlock` commits). In any bucket, a safe-range one too (the compaction's; 3.1: which
keys the readers may then miss is `Unlock`'s deleting branch's premise, `thinV`), but not at a hook's
own key (`P.hk`); in a tracked bucket (`P.RB`, D22, 2026-10-23) with the client's half of
the tracked buckets (`rbPut`), given back updated. The key is the caller's slice (`own`) or one read
from the transaction itself (`txBytes`: the compaction deletes the keys its range returned). (Until
question 2, 2026-10-29: not in a safe-range bucket, an owned key only; a Draft `specC` had this
statement beside it, with a premise `dlIs` at a safe-range key that nothing used: review round 12,
R12-1.) -/
abbrev backend.batchTxBuffered.UnsafeDelete.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess)
    (bk : GoInterface) (bi : BucketInfo) (key : GoSlice) (kb : GoString) (dk : DFrac) (own : Bool),
  P.has bi → sint.Z st.pend + 1 < 2 ^ 58 → P.hk bi.name kb = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi ∗
      (if own then key ↦*{dk} kb else txBytes st.tx key kb) ∗
      rbPut γ P bi.name st.S }}
    (App (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafeDelete")) (Val #bk)) (Val #key))
  {{ RET #(); batchLocked γ P b (st.del bi kb) ∗
      (if own then key ↦*{dk} kb else txBytes st.tx key kb) ∗ rbPut γ P bi.name (st.del bi kb).S }}

end spec

end EtcdGrove
end Perennial
