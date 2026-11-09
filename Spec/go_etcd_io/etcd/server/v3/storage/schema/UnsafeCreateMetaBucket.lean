/-
## `schema.UnsafeCreateMetaBucket(tx)`

**Users.** `mvcc.NewStore` (`kvstore.go:123`: the store's batch transaction, its lock held; mvcc's
storage contract, 3e, whose part includes `Meta`'s existence). Snippet: `examples/specreq/schema/schema.go`
(`ReqCreateBuckets`).

**Proof sketch.** Loads `Meta` (`bucketVars_init`: `bucketAt .metaB`), `tx.UnsafeCreateBucket(Meta)`
(`txWr`'s create).

**Changes.** From `specs-ref`'s `UnsafeCreateMetaBucket.lean` (over the real backend's batch
state): over the transaction contract. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Schema

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **Creates `Meta`** (if absent). -/
def UnsafeCreateMetaBucket.spec : Prop :=
  ∀ (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txWr tx S R ∗ R V ∗ ⌜S.whole .metaB⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.UnsafeCreateMetaBucket)) (Val #tx))
  {{ RET #(); R (V.create .metaB) }}

end spec
end Schema
end EtcdGrove
end Perennial
