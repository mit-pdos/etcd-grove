/-
## `(*batchTxBuffered).UnsafeCreateBucket(bucket)` (promoted `batchTx.UnsafeCreateBucket`, `batch_tx.go:142-151`): translated

**Users.** mvcc's `NewStore` (`kvstore.go:122`), the schema's bucket creations (4b: `auth.go:54-56`,
`alarm.go:49`, `lease.go`, `membership.go`, `cindex.go`'s `Meta`, `auth_roles.go:26`). Snippet
`parts.go`.

**Proof sketch.** bbolt's `CreateBucketIfNotExists` (4c: an existing bucket unchanged; an error is
`lg.Fatal`), `pending++`. Either the caller owns the bucket's existence cell, or the bucket exists
for good (`beMade`: the session's image has it, `beMade_cur`, a no-op).

**Changes** (from `specs-ref`'s): the shared `Meta` bucket by `beMade`. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

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

/-- **`t.UnsafeCreateBucket(bk)`**: `bk`'s bucket exists in the batch image (`o`: the caller's part
holding its existence cell, or `none` when it exists for good). -/
def batchTxBuffered.UnsafeCreateBucket.spec : Prop :=
  ∀ (γ : BeNames) (q : Qp) (F : Fp) (S : Sess) (bk : GoInterface) (bi : BktInfo)
    (o : Option (Fp × Image)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beSess γ q F S ∗ bkt γ bk bi ∗
      (match o with
       | some (G, C) => beCur γ G C ∗ ⌜G (.bkt bi.name)⌝ ∗ writable γ F (Fp.bkt bi.name)
       | none => beMade γ bi.name) }}
    (App (Val ((btLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty @!! go!"UnsafeCreateBucket")) (Val #bk))
  {{ RET #(); beSess γ q F (S.create bi.name) ∗
      (match o with
       | some (G, C) => beCur γ G (C.create bi.name)
       | none => beMade γ bi.name) }}

end spec

end Backend
end EtcdGrove
end Perennial
