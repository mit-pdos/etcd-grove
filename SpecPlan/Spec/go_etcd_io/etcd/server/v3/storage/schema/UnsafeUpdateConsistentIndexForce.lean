/-
## `schema.UnsafeUpdateConsistentIndexForce(tx, index, term)`

**Users.** `cindex.UpdateConsistentIndexForTest`-like `SetConsistentIndex` paths (`cindex.go:177`: `unsafeUpdateConsistentIndexForce`, used by `etcdutl` snapshot restore and tests). Snippet: `examples/specreq/schema/schema.go` (`ReqSaveThenRead`).

**Proof sketch.** As `unsafeUpdateConsistentIndex` with `allowDecreasing`: no read.

**Changes.** From `specs-ref`'s `UnsafeUpdateConsistentIndexForce.lean`.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.schema.Api
public import SpecPlan.Spec.go_etcd_io.etcd.client.pkg.v3.verify.Api

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

/-- **Writes the index (unless `0`) and the term (unless `0`), with no check.** -/
def UnsafeUpdateConsistentIndexForce.spec : Prop :=
  ∀ (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData) (i t : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txWr tx S R ∗ R V ∗ ⌜S.has .metaB ciKey ∧ S.has .metaB termKey⌝ ∗
      ⌜i ≠ W64 0 → V .metaB = some m⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.UnsafeUpdateConsistentIndexForce)) (Val #tx)) (Val #i)) (Val #t))
  {{ RET #(); R (if i = W64 0 then V else V.set .metaB (ciPut m i t)) }}

end spec
end Schema
end EtcdGrove
end Perennial
