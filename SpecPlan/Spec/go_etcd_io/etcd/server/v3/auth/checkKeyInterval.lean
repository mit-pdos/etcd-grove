/-
## `checkKeyInterval(lg, cachedPerms, key, rangeEnd, permtyp)` (internal helper)

**Users.** `isRangeOpPermitted` (a non-empty `rangeEnd`).

**Proof sketch.** `isOpenEnded` (then `nil`, the tree's infinity); `adt.NewBytesAffineInterval(key, rangeEnd)`; the read or write tree's `Contains` (3f: the union of the stored intervals covers the interval; for an empty or inverted interval, any answer). With `validPerms a` the stored intervals have non-empty keys, so `Contains` never covers the empty key.
Integration I5: 3f's `intervalTree.Contains.spec` is exact only for `affLt b e`; with the empty `key`
(the affine top, so `affLt` fails) and a proper or open end, this spec's `true → covers` needs
`Contains` to answer `false` (Go: `Visit` of a query from the top meets nothing, `minBegin` stays
`nil`): requested of 3f (`req/go_etcd_io_etcd_pkg_v3_adt.md`, "from 3d", item 3, still open). Another permission type: `lg.Panic`, ruled out by the premise.

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

/-- **`checkKeyInterval`** of a cache entry of `u` at `a`: covered at `a` exactly, but for an inverted
range, which may be refused. -/
def checkKeyInterval.spec : Prop :=
  ∀ (lg p : Loc) (a : AuthState) (u : GoString) (key re : GoSlice) (dk de : DFrac) (k e : List w8)
    (pt : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ Zap.isLogger lg ∗ cacheEntry p a u ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ ⌜e ≠ []⌝ ∗
      ⌜validPerms a ∧ (pt = W32 0 ∨ pt = W32 1) ∧ sint.Z key.len < 2 ^ 63 - 1 ∧
        sint.Z re.len < 2 ^ 63 - 1⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.checkKeyInterval)) (Val #lg)) (Val #p)) (Val #key)) (Val #re)) (Val #pt))
  {{ (b : Bool), RET #b; key ↦*{dk} k ∗ re ↦*{de} e ∗
      ⌜(b = true → a.covers u (ptOf pt) { key := k, rangeEnd := e }) ∧
       (b = false → ¬ a.covers u (ptOf pt) { key := k, rangeEnd := e } ∨ rngInverted { key := k, rangeEnd := e })⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial
