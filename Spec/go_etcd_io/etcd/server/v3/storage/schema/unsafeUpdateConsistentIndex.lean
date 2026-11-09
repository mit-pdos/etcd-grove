/-
## `schema.unsafeUpdateConsistentIndex(tx, index, term, allowDecreasing)` (internal)

**Users.** `UnsafeUpdateConsistentIndex`, `UnsafeUpdateConsistentIndexForce`. **Proof sketch.** See
`UnsafeUpdateConsistentIndex`; with `allowDecreasing` no read, and with `ETCD_VERIFY` off
`verify.Verify` does not run its closure (no read either: integration, the wrapper's
`verifyOff` branch has no `txRd` to give). **Changes.** From `specs-ref`'s
`unsafeUpdateConsistentIndex.lean`.
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

/-- Writes the index and term (`ciPut`), checking the index does not decrease unless allowed. -/
def unsafeUpdateConsistentIndex.spec : Prop :=
  ∀ (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData) (i t : w64)
    (allow : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txWr tx S R ∗ R V ∗ ⌜S.has .metaB ciKey ∧ S.has .metaB termKey⌝ ∗
      ⌜i ≠ W64 0 → V .metaB = some m⌝ ∗
      (⌜allow = true⌝ ∨ Verify.verifyOff ∨ (txRd tx S R ∗ ⌜i ≠ W64 0 → ciWf m⌝ ∗ ⌜i = W64 0 ∨ uint.Z (ciOf m).1 ≤ uint.Z i⌝)) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.unsafeUpdateConsistentIndex)) (Val #tx)) (Val #i)) (Val #t)) (Val #allow))
  {{ RET #(); R (if i = W64 0 then V else V.set .metaB (ciPut m i t)) }}

end spec
end Schema
end EtcdGrove
end Perennial
