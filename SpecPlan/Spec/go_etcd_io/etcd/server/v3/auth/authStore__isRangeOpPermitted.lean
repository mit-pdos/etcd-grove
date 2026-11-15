/-
## `(*authStore).isRangeOpPermitted(userName, key, rangeEnd, permtyp)` (internal helper)

**Users.** `isOpPermitted`.

**Proof sketch.** `rangePermCacheMu.RLock()` (a reader slot: `threadTok`), the map (the cache view, at a recorded state `ac`: each entry `cacheEntry`), the user's entry (absent: `false`); `checkKeyPoint` for an empty `rangeEnd`, else `checkKeyInterval` (their specs, with `validPerms ac`: `authAt_valid`).

**Changes.** The old spec restated over `Api.lean`'s and `Internal.lean`'s vocabulary.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.auth.authStore__isOpPermitted

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

/-- **`as.isRangeOpPermitted(u, key, rangeEnd, pt)`**: the cache view's verdict at a recorded state:
`true` only if covered there; `false` only if not covered there, or the range is inverted. -/
def authStore.isRangeOpPermitted.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (i0 : Nat) (u : GoString) (key re : GoSlice)
    (dk de : DFrac) (k e : List w8) (pt : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authLb γa i0 ∗ threadTok ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗
      ⌜(pt = W32 0 ∨ pt = W32 1) ∧ sint.Z key.len < 2 ^ 63 - 1 ∧ sint.Z re.len < 2 ^ 63 - 1⌝ }}
    (App (App (App (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"isRangeOpPermitted")) (Val #u)) (Val #key)) (Val #re)) (Val #pt))
  {{ (b : Bool), RET #b; threadTok ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗
      ∃ (jc : Nat) (ac : AuthState), ⌜i0 ≤ jc⌝ ∗ authAt γa jc ac ∗
        ⌜(b = true → ac.covers u (ptOf pt) { key := k, rangeEnd := e }) ∧
         (b = false → ¬ ac.covers u (ptOf pt) { key := k, rangeEnd := e } ∨
            rngInverted { key := k, rangeEnd := e })⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial
