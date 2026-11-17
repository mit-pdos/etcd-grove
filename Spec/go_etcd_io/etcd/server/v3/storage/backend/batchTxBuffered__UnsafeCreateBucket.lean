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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `t.UnsafeCreateBucket(bucket)` under the lock (a name of `1..MaxKeySize` bytes): the bucket,
empty if it was absent; a tracked bucket (`P.RB`, D22, 2026-10-23) with the client's part of
that bucket (`rbPut`: since decision 3, 2026-11-01, of its bucket only), given back updated. (A1.4 of `auth-schema-srv`, 2026-11-17) In either mode `c` of the batch lock, with the part of either kind
(`k`: the claimed part, only in a claimed session; a creation changes no kind, so it records no claimed
write). -/
abbrev backend.batchTxBuffered.UnsafeCreateBucket.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface) (bi : BucketInfo),
  P.has bi → 0 < bi.name.length → bi.name.length ≤ maxKeySize → sint.Z st.pend + 1 < 2 ^ 58 →
  ∀ (c k : Bool) {_hkc : k ≤ c},
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st c ∗ isBucket bk bi ∗ rbPut γ P bi.name st.S k }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafeCreateBucket")) (Val #bk))
  {{ RET #(); batchLocked γ P b (st.create bi) c ∗ rbPut γ P bi.name (st.create bi).S k }}

end spec

end EtcdGrove
end Perennial
