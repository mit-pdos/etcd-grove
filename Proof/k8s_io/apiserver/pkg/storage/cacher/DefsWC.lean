/-
**The watch cache, as the specs of its reads see it** (KEP-6404, `notes/kep-6404-plan.md`;
2026-10-26). Lean-first (no Rocq counterpart).

`watchCache` (`watch_cache.go`) holds, under its own lock (its embedded `RWMutex`), the resource
version it has caught up to (`resourceVersion`), and the store (`storage`, a `WatchCacheStorage`,
`store/DefsWCS.lean`), whose writes it calls under the lock (`processEvent`,
`UpdateResourceVersion`). Readers wait under the read lock until the cache is fresh enough
(`waitUntilFreshLocked`, on `cond`, a condition variable over the read lock, `sync.NewCond(
wc.RLocker())`), then load the store's latest snapshot.

* `wcLockP wc γ q`: the lock's resource at fraction `q`: the cache's `resourceVersion` and the
  store's writer token (`wcsOwn γ q st`, `DefsWCS.lean`) of one state `st`, the version its second
  component. A reader (`q = rfrac`) knows the store's state; a writer (`q = 1`) can write it.
* `clockOk clk`: the configuration's clock (`clock.Clock`, names-only; `clock.RealClock` from the
  cacher): `Now` and `Since` return, and `After`'s channel can be received from (it may block).
* `cfgOk cfg`: the configuration's fields the reads use, read-only for good (the configuration is
  immutable): the clock, the progress requester (`isPR`), and the resource's group and name, valid
  UTF-8 (the read-wait histogram's labels).
* `isWC wc γ Ψ`: the store (`isWCS`, with the caller's fact `Ψ` of every state it publishes), the
  condition variable over the read lock, the configuration, and the lock's writer guard.
* `wcGetOk wc parseRV ctxPre curRV`: the configuration's fields a GET uses to find the version to
  wait for (`WaitUntilFreshAndGet`): the versioner (an interface, from the cacher's `Config`),
  whose `ParseResourceVersion` returns `parseRV s` (or an error if it is `none`), and
  `getCurrentRV` (a function, from the cacher: the etcd3 store's `GetCurrentResourceVersion`, a
  quorum read of etcd), which, on a context with `ctxPre` (the store's: `ctxOk`, `ctxErrClient`),
  returns a result `n` that comes with `curRV n` without an error. `curRV` is persistent in effect (it is under the `□`), so
  it is not an atomic update fired inside the call; a caller re-establishes `wcGetOk` for each GET
  with a fact of that call: for a linearizable read, `curRV n := ⌜r0 ≤ n⌝` for a lower bound `r0`
  of etcd's revision taken at the call's start (from a spec of `getCurrentRV` that, given the
  bound `r`, returns `n ≥ r`; `notes/kep-6404-plan.md`, step 2).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.store.DefsWCS
public import Proof.k8s_io.apiserver.pkg.storage.cacher.progress.Defs
public import Proof.unicode.utf8.Valid

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI k8s_io.apiserver.pkg.storage.cacher

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- The lock's resource at fraction `q`, of the state `st` (see the file header). -/
def wcLockPSt (wc : Loc) (γ : WCSNames) (q : Qp) (st : SnapSt) : IProp GF :=
  iprop(structFieldRef watchCache go!"resourceVersion" wc ↦{DFrac.own q} st.2 ∗ wcsOwn γ q st)

/-- **The lock's resource at fraction `q`** (see the file header). -/
def wcLockP (wc : Loc) (γ : WCSNames) (q : Qp) : IProp GF :=
  iprop(∃ st : SnapSt, wcLockPSt wc γ q st)

/-- A channel that can be received from (`clock.After`'s). -/
def chanRecvOk (ch : Loc) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ (v : _root_.Perennial.time.Time) (ok : Bool), Φ (PairV #v #ok)) -∗
    WP (App (Val (chan.receive _root_.Perennial.time.Time.ty)) (Val #ch)) {{ Φ }})

instance chanRecvOk_persistent (ch : Loc) : Persistent (chanRecvOk (GF := GF) ch) := by
  unfold chanRecvOk; infer_instance

/-- **The configuration's clock** (see the file header). -/
def clockOk (clk : GoInterfaceOk) : IProp GF :=
  iprop(□ (∀ Φ : val → IProp GF, ▷ (∀ t : _root_.Perennial.time.Time, Φ #t) -∗
      WP (App (Val #(methods clk.ty go!"Now" clk.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ (t : _root_.Perennial.time.Time) (Φ : val → IProp GF),
      ▷ (∀ d : _root_.Perennial.time.Duration, Φ #d) -∗
      WP (App (Val #(methods clk.ty go!"Since" clk.v)) (Val #t)) {{ Φ }}) ∗
    □ (∀ (d : _root_.Perennial.time.Duration) (Φ : val → IProp GF),
      ▷ (∀ ch : Loc, chanRecvOk ch -∗ Φ #ch) -∗
      WP (App (Val #(methods clk.ty go!"After" clk.v)) (Val #d)) {{ Φ }}))

instance clockOk_persistent (clk : GoInterfaceOk) : Persistent (clockOk (GF := GF) clk) := by
  unfold clockOk; infer_instance

/-- **The configuration's fields the reads use** (see the file header). -/
def cfgOk (cfg : Loc) : IProp GF :=
  iprop(∃ (clk : GoInterfaceOk) (pr : Loc) (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource),
    structFieldRef ImmutableWatchCacheConfig go!"clock" cfg ↦□ GoInterface.ok clk ∗ clockOk clk ∗
    structFieldRef ImmutableWatchCacheConfig go!"waitingUntilFresh" cfg ↦□ pr ∗ isPR (GF := GF) pr ∗
    structFieldRef ImmutableWatchCacheConfig go!"groupResource" cfg ↦□ gr ∗
    ⌜utf8Valid gr.Group' ∧ utf8Valid gr.Resource'⌝)

instance cfgOk_persistent (cfg : Loc) : Persistent (cfgOk (GF := GF) cfg) := by
  unfold cfgOk; infer_instance

/-- **`wc` is a watch cache** (persistent; see the file header). -/
def isWC (wc : Loc) (γ : WCSNames) (Ψ : SnapSt → IProp GF) : IProp GF :=
  iprop(∃ (s c cfg : Loc),
    structFieldRef watchCache go!"storage" wc ↦□ s ∗ isWCS s γ Ψ ∗
    structFieldRef watchCache go!"cond" wc ↦□ c ∗ sync.isCond (GF := GF) c (sync.rlockerOf (structFieldRef watchCache go!"RWMutex" wc)) ∗
    structFieldRef watchCache go!"config" wc ↦□ cfg ∗ cfgOk cfg ∗
    sync.isRWMutexGuard (structFieldRef watchCache go!"RWMutex" wc) (wcLockP wc γ))

instance isWC_persistent (wc : Loc) (γ : WCSNames) (Ψ : SnapSt → IProp GF) :
    Persistent (isWC (GF := GF) wc γ Ψ) := by
  unfold isWC; infer_instance

/-- **The configuration's fields a GET uses to find its version** (persistent; see the file
header). -/
def wcGetOk (wc : Loc) (parseRV : GoString → Option w64) (ctxPre : GoInterface → IProp GF)
    (curRV : w64 → IProp GF) : IProp GF :=
  iprop(∃ (cfg : Loc) (vi : GoInterfaceOk) (f : GoFunc),
    structFieldRef watchCache go!"config" wc ↦□ cfg ∗
    structFieldRef ImmutableWatchCacheConfig go!"versioner" cfg ↦□ GoInterface.ok vi ∗
    structFieldRef ImmutableWatchCacheConfig go!"getCurrentRV" cfg ↦□ f ∗
    □ (∀ (s : GoString) (Φ : val → IProp GF),
      ▷ (∀ (n : w64) (err : GoInterface),
          ⌜match parseRV s with
            | some m => err = GoInterface.nil ∧ n = m
            | none => err ≠ GoInterface.nil⌝ -∗ Φ (PairV #n #err)) -∗
      WP (App (Val #(methods vi.ty go!"ParseResourceVersion" vi.v)) (Val #s)) {{ Φ }}) ∗
    □ (∀ (ctx : GoInterface) (Φ : val → IProp GF), ctxPre ctx -∗
      ▷ (∀ (n : w64) (err : GoInterface), (⌜err = GoInterface.nil⌝ -∗ curRV n) -∗
          Φ (PairV #n #err)) -∗
      WP (App (Val #f) (Val #ctx)) {{ Φ }}))

instance wcGetOk_persistent (wc : Loc) (parseRV : GoString → Option w64)
    (ctxPre : GoInterface → IProp GF) (curRV : w64 → IProp GF) :
    Persistent (wcGetOk (GF := GF) wc parseRV ctxPre curRV) := by
  unfold wcGetOk; infer_instance

end defs

end cacher
end EtcdGrove
end Perennial
