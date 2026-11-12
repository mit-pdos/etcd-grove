/-
## `(*batchTxBuffered).UnsafePut(bucket, key, value)` (`batch_tx.go:402-405`): translated

**Users.** mvcc's compaction keys (`store.go:42, 56`), the schema's writers (4b: meta, lease, auth,
membership, alarm, version), the hooks' consistent index and configuration (`cindex.go`,
`confstate.go`, through the `UnsafeReadWriter` value). Snippet `parts.go`.

**Proof sketch.** `batchTx.UnsafePut` (`unsafePut`: `t.tx.Bucket(name)`, nil is `lg.Fatal`; bbolt's
`Put` (4c, under its size bound `bboltEntryMax`; its errors, an empty or oversized key, are
`lg.Fatal`): the bbolt transaction's data, the batch image, at `put`; `pending++`), then the write
buffer's `put` (the bucket marked non-sequential: sorted and deduplicated at the write-back). The
cell's part agrees with the session's image (`beSess_cur`) and moves with it; a cell the session
publishes, or one no client tracks, may change (`writable`). In a safe-range bucket the key is new
and above every key (`Sess.fresh`): the read buffer and bbolt's read transaction then hold disjoint
keys, the buffer's above (what `rdRange` assumes), and a non-blocking defragmentation's catch-up
copies it.

**Changes** (from `specs-ref`'s, `P.SB` premises over `BSess`): over the session and the cell's part;
`bboltEntryMax` (4c's bound) in place of `keySized`.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`t.UnsafePut(bk, k, v)`**: the batch image at `k := v` in `bk`'s bucket; the cell's part
moves with it. -/
def batchTxBuffered.UnsafePut.spec : Prop :=
  ∀ (γ : BeNames) (q : Qp) (F : Fp) (S : Sess) (G : Fp) (C : Image) (bk : GoInterface)
    (bi : BktInfo) (ks vs : GoSlice) (k v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beSess γ q F S ∗ bkt γ bk bi ∗ beCur γ G C ∗ ⌜G (.key bi.name k)⌝ ∗
      writable γ F (Fp.key bi.name k) ∗ ⌜bi.safe = true → S.fresh bi.name k⌝ ∗
      ⌜k.length + v.length ≤ Bbolt.bboltEntryMax⌝ ∗ ks ↦*□ k ∗ vs ↦*□ v }}
    (App (App (App (Val ((btLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty @!! go!"UnsafePut")) (Val #bk)) (Val #ks)) (Val #vs))
  {{ RET #(); beSess γ q F (S.put bi.name k v) ∗ beCur γ G (C.put bi.name k v) }}

end spec

end Backend
end EtcdGrove
end Perennial
