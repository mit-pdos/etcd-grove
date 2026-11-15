/-
## `checkKeyPoint(lg, cachedPerms, key, permtyp)` (internal helper)

**Users.** `isRangeOpPermitted` (an empty `rangeEnd`).

**Proof sketch.** `adt.NewBytesAffinePoint(key)`; the tree's `Intersects` (3f). Another type: `lg.Panic`, ruled out.

**Changes.** The old spec restated over `Api.lean`'s and `Internal.lean`'s vocabulary.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.auth.authStore__isOpPermitted
public import SpecPlan.Spec.go_uber_org.zap.Api
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.auth.Internal

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Auth

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`checkKeyPoint`** of a cache entry of `u` at `a`: covered at `a` exactly, but for an inverted
range, which may be refused. -/
def checkKeyPoint.spec : Prop :=
  ∀ (lg p : Loc) (a : AuthState) (u : GoString) (key : GoSlice) (dk : DFrac) (k : List w8)
    (pt : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ Zap.isLogger lg ∗ cacheEntry p a u ∗ key ↦*{dk} k ∗
      ⌜validPerms a ∧ (pt = W32 0 ∨ pt = W32 1) ∧ sint.Z key.len < 2 ^ 63 - 1⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.checkKeyPoint)) (Val #lg)) (Val #p)) (Val #key)) (Val #pt))
  {{ (b : Bool), RET #b; key ↦*{dk} k ∗
      ⌜(b = true → a.covers u (ptOf pt) { key := k, rangeEnd := [] }) ∧
       (b = false → ¬ a.covers u (ptOf pt) { key := k, rangeEnd := [] } ∨ rngInverted { key := k, rangeEnd := [] })⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial
