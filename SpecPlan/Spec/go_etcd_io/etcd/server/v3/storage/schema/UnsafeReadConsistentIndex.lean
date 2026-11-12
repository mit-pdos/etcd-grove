/-
## `schema.UnsafeReadConsistentIndex(tx)`

**Users.** `ReadConsistentIndex`; `cindex.UnsafeConsistentIndex` (`cindex.go:107`: `ci.be.ReadTx()`
without `RLock`, from the post-lock hook, which holds the batch lock: 2d, whose `R` the backend must
give for that case); `unsafeUpdateConsistentIndex`'s check. Snippet: `examples/specreq/schema/schema.go`
(`ReqSaveThenRead`).

**Proof sketch.** Loads `Meta` and the key names (`bucketVars_init`, `keyNames_init`);
`tx.UnsafeRange(Meta, consistent_index, nil, 0)` (`txRd`: the key alone); none: `(0, 0)`; else
`binary.BigEndian.Uint64(vs[0])` (`ciWf`: eight bytes) and the same for `term`.

**Changes.** From `specs-ref`'s `UnsafeReadConsistentIndex.lean` (`metaReader`/`readCIAUA`, two
linearizable reads under the old cindex invariant): one view `R V` held across both reads (a read
transaction's snapshot, or the batch view under its lock), so the pair is consistent.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.schema.Api

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

/-- **The stored consistent index and term** (`ciOf`: `0` where absent). -/
def UnsafeReadConsistentIndex.spec : Prop :=
  ∀ (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txRd tx S R ∗ R V ∗ ⌜S.has .metaB ciKey ∧ S.has .metaB termKey⌝ ∗
      ⌜V .metaB = some m ∧ ciWf m⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.UnsafeReadConsistentIndex)) (Val #tx))
  {{ RET (PairV #(ciOf m).1 #(ciOf m).2); R V }}

end spec
end Schema
end EtcdGrove
end Perennial
