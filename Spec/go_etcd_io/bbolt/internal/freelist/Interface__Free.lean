/-
## `Interface.Free(txid, p)` (`shared.go`)

**Users.** node.go:325 (`spill`: a node's old page), node.go:502 (`node.free`: a rebalanced-away node), bucket.go:915 (`Bucket.free`: a deleted bucket's pages), tx.go:217 (`Commit`: the old freelist page). Snippet `ReqAllocFree`.
**Proof sketch.** the bundle's triple: the dynamic type is a `*array` or a `*hashMap` (`flOwn`'s realization), whose method (or `shared`'s, promoted) is proved against the realization's invariant; `p.Id()`, `p.Overflow()` (`BboltCommon`'s page specs, at the page's share), `allocs` moved to the pending entry, `Verify`'s check (premise), per slot the `cache` check (premise) and the appends.
**Changes.** from `specs-ref`'s `Interface__Free.lean`: over `FLState` and the page's bytes (`hdrOf`).
**Margin.** none: the post is what the code computes.
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Api

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

/-- `f.Free(txid, p)`: the page `p` and its overflow pages are pending for `txid` (`FLState.freeRun`). It panics on page 0 or 1, a page already free or pending, or (`Verify`) a page `txid` allocated: `canFree` excludes them. The page's bytes are read at any share. -/
def Interface.Free.spec : Prop :=
  ∀ (fl : GoInterface) (F : FLState) (txid : Txid) (p : Loc) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ bytesPointsto p dq bs ∗
      ⌜pageHeaderSize ≤ bs.length ∧
        F.canFree txid (hdrOf bs).id' ((hdrOf bs).overflow'.toNat + 1)⌝ }}
    (App (App (flCall fl go!"Free") (Val #txid)) (Val #p))
  {{ RET #(); flOwn fl (F.freeRun txid (hdrOf bs).id' ((hdrOf bs).overflow'.toNat + 1)) ∗
      bytesPointsto p dq bs }}

end spec

end Freelist
end EtcdGrove
end Perennial
