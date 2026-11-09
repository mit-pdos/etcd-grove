/-
## `Interface.ReleasePendingPages()` (`shared.go`)

**Users.** db.go:944 (`beginRWTx`, under `rwlock` and `metalock`: before the writer allocates). Snippet `ReqReleaseSafe`.
**Proof sketch.** the interface's contract (`Interface.<M>.contract`), proved at each dynamic type (`array.<M>.spec`, `hashMap.<M>.spec`: the method, or `shared`'s promoted one, against `flOwn`'s realization); the interface call is then the instance at `flCall` by `flOwn_dyn`: sorts `readonlyTXIDs` (Perennial's `sort.Sort`: its size bound), `release(minid - 1)` (every page freed before the oldest reader), then `releaseRange` over each gap between readers and after the last: a page freed and allocated in one gap has no reader between, so it is releasable; the skip on `lastReleaseBegin` only releases fewer. `mergeSpans` (array: `Pgids.Merge`; hash map: span merging, its `Verify` check through `reflect.DeepEqual`, trusted, `req/reflect.md`).
**Changes.** from `specs-ref`'s `Interface__ReleasePendingPages.lean`: the released set characterized (releasable, and at least the pages freed before every reader) instead of the code's `release`/`releaseRange` replayed with `lastReleaseBegin`; the readers as their own resource. New premise `readersOk`: a reader with txid 0 makes `releaseRange(0, 2^64-1)` release every pending page, including the pages that reader sees (see `notes/specs-only/batch-4d.md`).
**Margin.** which releasable pages beyond `mustRelease` are released (those freed and allocated between two readers, unless the entry was already looked at from the same gap's start) is left open.
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

/-- The contract of `ReleasePendingPages` at a freelist `fl` whose method is the expression `f` (the bundle's triple; each concrete spec is its instance). `f.ReleasePendingPages()` with the readers `R`: some set `S` of pending pages becomes free, each releasable (no reader sees it), including every page freed before all readers. -/
def Interface.ReleasePendingPages.contract (fl : GoInterface) (f : Expr) : Prop :=
  ∀ (F : FLState) (R : List Txid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ flReaders fl R ∗
      ⌜readersOk R ∧ R.length < 2 ^ 62 ∧ F.count < flMaxIds⌝ }}
    (App f (Val #()))
  {{ RET #(); ∃ S : GMap Pgid Unit,
      ⌜(∀ p, p ∈ S → F.releasable R p) ∧ (∀ p, F.mustRelease R p → p ∈ S)⌝ ∗
      flOwn fl (F.release S) ∗ flReaders fl R }}

/-- `f.ReleasePendingPages()` with the readers `R`: some set `S` of pending pages becomes free, each releasable (no reader sees it), including every page freed before all readers. Through the interface (`flCall`): proved from `array.ReleasePendingPages.spec`, `hashMap.ReleasePendingPages.spec` and `flOwn_dyn`/`flReaders_dyn` (Perennial's `method_interface_ok` steps the call to the dynamic type's method). -/
def Interface.ReleasePendingPages.spec : Prop := ∀ fl, Interface.ReleasePendingPages.contract (GF := GF) fl (flCall fl go!"ReleasePendingPages")

end spec

end Freelist
end EtcdGrove
end Perennial
