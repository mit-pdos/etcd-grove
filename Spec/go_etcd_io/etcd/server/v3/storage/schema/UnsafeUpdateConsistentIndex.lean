/-
## `schema.UnsafeUpdateConsistentIndex(tx, index, term)`

**Users.** `cindex.UnsafeSave` (`cindex.go:120`), from the backend's pre-commit hook (2e's `OnPreCommitUnsafe`), the batch lock held. Snippet: `examples/specreq/schema/schema.go` (`ReqSaveThenRead`).

**Proof sketch.** `i = 0`: return, before touching `tx` (the pre-commit hook of a commit before any entry is applied, `Meta` possibly absent: no premise on it then). `beU64` into fresh slices (read-only for good: `txWr`'s put keeps them); `verify.Verify` (1c's `Verify.spec`: `verifyOff`, or its closure, `UnsafeReadConsistentIndex(tx)` (`ciWf`) and the comparison, returns `true`); two puts (`txWr`).

**Changes.** From `specs-ref`'s `UnsafeUpdateConsistentIndex.lean`/`unsafeUpdateConsistentIndex.lean` (`metaWriter`, put tokens): over the contract; the check's premise is a disjunction on the environment, as `Verify`'s.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.Api
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Api

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

/-- **Writes the index (unless `0`) and the term (unless `0`), the index not decreasing (`ETCD_VERIFY` off, or the stored index at most `i`).** -/
def UnsafeUpdateConsistentIndex.spec : Prop :=
  ∀ (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData) (i t : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txWr tx S R ∗ txRd tx S R ∗ (Verify.verifyOff ∨ ⌜i = W64 0 ∨ uint.Z (ciOf m).1 ≤ uint.Z i⌝) ∗ R V ∗ ⌜S.has .metaB ciKey ∧ S.has .metaB termKey⌝ ∗
      ⌜i ≠ W64 0 → V .metaB = some m ∧ ciWf m⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.UnsafeUpdateConsistentIndex)) (Val #tx)) (Val #i)) (Val #t))
  {{ RET #(); R (if i = W64 0 then V else V.set .metaB (ciPut m i t)) }}

end spec
end Schema
end EtcdGrove
end Perennial
