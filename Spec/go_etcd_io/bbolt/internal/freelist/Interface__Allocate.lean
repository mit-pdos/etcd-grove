/-
## `Interface.Allocate(txid, n)` (`array.go`, `hashmap.go`)

**Users.** db.go:1250 (`DB.allocate`: `0` means "grow the file", else the run's first page). Snippet `ReqAllocFree`.
**Proof sketch.** the interface's contract (`Interface.<M>.contract`), proved at each dynamic type (`array.<M>.spec`, `hashMap.<M>.spec`: the method, or `shared`'s promoted one, against `flOwn`'s realization); the interface call is then the instance at `flCall` by `flOwn_dyn`; the array scans its sorted ids for the first run of `n` (panicking on an id below 2: `F.wf`), the hash map takes a span of exactly `n` or splits a larger one; both delete the run from `cache` and record `allocs[r] = txid`.
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

/-- The contract of `Allocate` at a freelist `fl` whose method is the expression `f` (the bundle's triple; each concrete spec is its instance). `f.Allocate(txid, n)` (`n > 0`): `0`, nothing changed; or the first page `r` of a run of `n` free pages, now allocated by `txid` (`FLState.alloc`). Which run is the implementation's. -/
def Interface.Allocate.contract (fl : GoInterface) (f : Expr) : Prop :=
  ∀ (F : FLState) (txid n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ ⌜0 < sint.Z n⌝ }}
    (App (App f (Val #txid)) (Val #n))
  {{ (r : w64), RET #r;
      (⌜r = W64 0⌝ ∗ flOwn fl F) ∨
      (⌜F.canAlloc r (sint.nat n)⌝ ∗ flOwn fl (F.alloc txid r (sint.nat n))) }}

/-- `f.Allocate(txid, n)` (`n > 0`): `0`, nothing changed; or the first page `r` of a run of `n` free pages, now allocated by `txid` (`FLState.alloc`). Which run is the implementation's. Through the interface (`flCall`): proved from `array.Allocate.spec`, `hashMap.Allocate.spec` and `flOwn_dyn`/`flReaders_dyn` (Perennial's `method_interface_ok` steps the call to the dynamic type's method). -/
def Interface.Allocate.spec : Prop := ∀ fl, Interface.Allocate.contract (GF := GF) fl (flCall fl go!"Allocate")

end spec

end Freelist
end EtcdGrove
end Perennial
