/-
## `Interface.Free(txid, p)` (`shared.go`)

**Users.** node.go:325 (`spill`: a node's old page), node.go:502 (`node.free`: a rebalanced-away node), bucket.go:915 (`Bucket.free`: a deleted bucket's pages), tx.go:217 (`Commit`: the old freelist page). Snippet `ReqAllocFree`.
**Proof sketch.** the interface's contract (`Interface.<M>.contract`), proved at each dynamic type (`array.<M>.spec`, `hashMap.<M>.spec`: the method, or `shared`'s promoted one, against `flOwn`'s realization); the interface call is then the instance at `flCall` by `flOwn_dyn`; `p.Id()`, `p.Overflow()` (`BboltCommon`'s page specs, at the page's share), `allocs` moved to the pending entry, `Verify`'s check (premise), per slot the `cache` check (premise) and the appends.
**Changes.** from `specs-ref`'s `Interface__Free.lean`: over `FLState` and the page's bytes (`hdrOf`).
**Margin.** none: the post is what the code computes.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.internal.freelist.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Freelist

open Iris Iris.BI go_etcd_io.bbolt.internal.common BboltCommon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- The contract of `Free` at a freelist `fl` whose method is the expression `f` (the bundle's triple; each concrete spec is its instance). `f.Free(txid, p)`: the page `p` and its overflow pages are pending for `txid` (`FLState.freeRun`). It panics on page 0 or 1, a page already free or pending, or (`Verify`) a page `txid` allocated: `canFree` excludes them. The page's bytes are read at any share. -/
def Interface.Free.contract (fl : GoInterface) (f : Expr) : Prop :=
  ∀ (F : FLState) (txid : Txid) (p : Loc) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ bytesPointsto p dq bs ∗
      ⌜pageHeaderSize ≤ bs.length ∧
        F.canFree txid (hdrOf bs).id' ((hdrOf bs).overflow'.toNat + 1)⌝ }}
    (App (App f (Val #txid)) (Val #p))
  {{ RET #(); flOwn fl (F.freeRun txid (hdrOf bs).id' ((hdrOf bs).overflow'.toNat + 1)) ∗
      bytesPointsto p dq bs }}

/-- `f.Free(txid, p)`: the page `p` and its overflow pages are pending for `txid` (`FLState.freeRun`). It panics on page 0 or 1, a page already free or pending, or (`Verify`) a page `txid` allocated: `canFree` excludes them. The page's bytes are read at any share. Through the interface (`flCall`): proved from `array.Free.spec`, `hashMap.Free.spec` and `flOwn_dyn`/`flReaders_dyn` (Perennial's `method_interface_ok` steps the call to the dynamic type's method). -/
def Interface.Free.spec : Prop := ∀ fl, Interface.Free.contract (GF := GF) fl (flCall fl go!"Free")

end spec

end Freelist
end EtcdGrove
end Perennial
