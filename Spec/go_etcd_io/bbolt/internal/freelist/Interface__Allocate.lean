/-
## `Interface.Allocate(txid, n)` (`array.go`, `hashmap.go`)

**Users.** db.go:1250 (`DB.allocate`: `0` means "grow the file", else the run's first page). Snippet `ReqAllocFree`.
**Proof sketch.** the bundle's triple: the dynamic type is a `*array` or a `*hashMap` (`flOwn`'s realization), whose method (or `shared`'s, promoted) is proved against the realization's invariant; the array scans its sorted ids for the first run of `n` (panicking on an id below 2: `F.wf`), the hash map takes a span of exactly `n` or splits a larger one; both delete the run from `cache` and record `allocs[r] = txid`.
**Changes.** from `specs-ref`'s `Interface__Allocate.lean`: over the abstract `FLState` (a set of free pages, not the array's list).
**Margin.** the array returns `0` only when no run of `n` exists, the hash map only when no span is long enough (its spans are maximal): a client may not rely on it (bbolt does not: it grows the file).
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

/-- `f.Allocate(txid, n)` (`n > 0`): `0`, nothing changed; or the first page `r` of a run of `n` free pages, now allocated by `txid` (`FLState.alloc`). Which run is the implementation's. -/
def Interface.Allocate.spec : Prop :=
  ∀ (fl : GoInterface) (F : FLState) (txid n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ ⌜0 < sint.Z n⌝ }}
    (App (App (flCall fl go!"Allocate") (Val #txid)) (Val #n))
  {{ (r : w64), RET #r;
      (⌜r = W64 0⌝ ∗ flOwn fl F) ∨
      (⌜F.canAlloc r (sint.nat n)⌝ ∗ flOwn fl (F.alloc txid r (sint.nat n))) }}

end spec

end Freelist
end EtcdGrove
end Perennial
