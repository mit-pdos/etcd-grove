/-
## `schema.ReadConsistentIndex(tx)`

**Users.** `cindex.ConsistentIndex` (`cindex.go:97`: `ci.be.ReadTx()`, while the in-memory index is
`0`), `storage.recoverSnapshotBackend` (`storage/backend.go:109`), `verify` (`server/verify`).
Snippet: `examples/specreq/schema/schema.go` (`ReqSaveThenRead`).

**Proof sketch.** `tx.RLock()` (`rdSect`: the caller's view `R V`, `Meta` present with `ciWf`),
`UnsafeReadConsistentIndex(tx)`, the deferred `tx.RUnlock()` (`rdSect`: `Q V`).

**Changes.** From `specs-ref`'s `ReadConsistentIndex.lean`: the read section's triples are the
caller's premise (`rdSect`): the snapshot's point and the reader slot are the backend's and the
caller's business (2d's `beStoredCI` is a realization of `R` and `Q`).

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

/-- **The consistent index and term of the view a read section sees.** -/
def ReadConsistentIndex.spec : Prop :=
  ∀ (tx : GoInterface) (S : Scope) (R : View → IProp GF) (P : IProp GF) (Q : View → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txRd tx S R ∗ ⌜S.has .metaB ciKey ∧ S.has .metaB termKey⌝ ∗
      rdSect tx P R (fun V => ∃ m, V .metaB = some m ∧ ciWf m) Q ∗ P }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.ReadConsistentIndex)) (Val #tx))
  {{ (i t : w64), RET (PairV #i #t); ∃ V m, Q V ∗ ⌜V .metaB = some m ∧ (i, t) = ciOf m⌝ }}

end spec
end Schema
end EtcdGrove
end Perennial
