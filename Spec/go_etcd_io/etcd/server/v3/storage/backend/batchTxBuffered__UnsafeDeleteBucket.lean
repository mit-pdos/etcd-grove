/-
`UnsafeDeleteBucket` (the backend). `t.UnsafeDeleteBucket(bucket)` under the lock: the bucket deleted (absent or not); a pending
delete.
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

/-- `t.UnsafeDeleteBucket(bucket)` under the lock: the bucket deleted (absent or not); a pending
delete. Not a safe-range bucket (`P.SB`), nor one with a hook's own key (`P.hk`) or a compaction
key (`fkKey`: the `meta` bucket, the M2 storage plan's items 27/29, 2026-10-30); a tracked bucket
(`P.RB`, D22, 2026-10-23) with the client's part of that bucket (`rbPut`: since decision 3,
2026-11-01, of its bucket only), given back updated. (A1.4 of `auth-schema-srv`, 2026-11-17) In either mode `c` of the batch lock (`true`: a claimed
session's), with the part of either kind (`k`: the claimed part `rbPutR`, only in a claimed session, the
write recorded as the bucket's claimed write `st.cw`); `c = k = false` is the statement until A1.4. -/
abbrev backend.batchTxBuffered.UnsafeDeleteBucket.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface) (bi : BucketInfo),
  P.has bi → sint.Z st.pend + 1 < 2 ^ 58 → P.SB bi.name = false → (∀ k, P.hk bi.name k = false) →
  (∀ k, ¬ fkKey bi.name k) →
  ∀ (c kc : Bool) {_hkc : kc ≤ c},
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st c ∗ isBucket bk bi ∗ rbPut γ P bi.name st.S kc }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafeDeleteBucket")) (Val #bk))
  {{ RET #(); batchLocked γ P b (st.delBucket bi kc) c ∗ rbPut γ P bi.name (st.delBucket bi kc).S kc }}

end spec

end EtcdGrove
end Perennial
