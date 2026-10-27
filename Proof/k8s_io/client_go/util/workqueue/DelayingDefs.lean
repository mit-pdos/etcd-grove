/-
The delaying queue (`delaying_queue.go`) and the rate-limiting queue (`rate_limiting_queue.go`).
Lean-first; phase 2 of the DaemonSet plan.

**The clock** `isClock c` (persistent): the `clock.Clock` (or `clock.WithTicker`) interface value
`c` whose `Now()` returns some time, `NewTimer(d)` a timer, `NewTicker(d)` (`d > 0`) a ticker; a
timer's or ticker's `C()` is a channel on which a receive may yield some time (Perennial's
timers: a bag of times, no logical content), `Stop()` returns. `RealClock{}` is one
(`realClock_isClock`, over the trust-boundary specs of `k8s.io/utils/clock`'s `RealClock`).

**The waiting heap**: a `waitForPriorityQueue[T]` (a `[]*waitFor[T]`) holding the entries `ws`
(pointer, item), each entry's `data` read-only and its `index` its position (`heap.Fix(q,
existing.index)` in `insert` needs it in range); `container/heap`'s contract over it
(`heap.heapIface`, `heap.heapPopIface`: `DelayingLemmas.lean`). The waiting loop's map
`waitingEntryByData` holds exactly the heap's entries, by item, no item twice (`byDataOk`).

**The delaying queue** `isDelaying q γ` (persistent): a `*delayingType[T]` over a typed queue
(`isTyped`, its embedded `TypedInterface`), with its clock, its stop channel (closed once, by
`ShutDown`, after the typed queue is shutting down: a broadcast of `shutdownLb`), its `stopOnce`
(which holds the stop channel's closing right and one shutdown token of the typed queue), its
heartbeat ticker, its channel `waitingForAddCh` of entries (a bag: a sent `*waitFor` is owned by
whoever receives it), its retry metrics (whose `retry()` returns).

**The rate-limiting queue** `isRateLimitingQueue q γ P` (persistent): a `*rateLimitingType[T]`
over a delaying queue and a rate limiter whose `When` satisfies `P`.

What is not stated: when (or whether) an item given to `AddAfter` is added. That is liveness: the
waiting loop adds each entry it receives once its time has come (or at once), unless the queue
is shut down first; the specs say only that nothing it does is unsafe.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.RateLimiterDefs
public import Spec.k8s_io.utils.clock.RealClock__NewTimer
public import Spec.k8s_io.utils.clock.RealClock__NewTicker
public import Proof.container.heap.Defs
public import Spec.container.heap.Pop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

/-- The ghost names of a delaying queue: its typed queue's, its stop channel's, its entry
channel's. -/
structure DNames where
  tq : QNames
  stop : ChanNames
  wch : ChanNames

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {K : Type} {T : go.GoType} [QItem (GF := GF) K T]

/-! ### The clock -/

/-- A `clock.Timer` (persistent): `C()` a channel of times, `Stop()` returns. -/
def isTimerI (tm : k8s_io.utils.clock.Timer) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜tm = interface.ok i⌝ ∗
    {{ (True : IProp GF) }} (App (Val #(methods i.ty go!"C" i.v)) (Val #()))
      {{ (ch : Loc) (γ : ChanNames), RET #ch; isChanBag γ ch (V := time.Time) (fun _ => iprop(True)) }} ∗
    {{ (True : IProp GF) }} (App (Val #(methods i.ty go!"Stop" i.v)) (Val #()))
      {{ (b : Bool), RET #b; True }})

instance isTimerI_persistent (tm : k8s_io.utils.clock.Timer) :
    Persistent (isTimerI (GF := GF) tm) := by
  unfold isTimerI; infer_instance

/-- A `clock.Ticker` (persistent): `C()` a channel of times, `Stop()` returns. -/
def isTickerI (tk : k8s_io.utils.clock.Ticker) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜tk = interface.ok i⌝ ∗
    {{ (True : IProp GF) }} (App (Val #(methods i.ty go!"C" i.v)) (Val #()))
      {{ (ch : Loc) (γ : ChanNames), RET #ch; isChanBag γ ch (V := time.Time) (fun _ => iprop(True)) }} ∗
    {{ (True : IProp GF) }} (App (Val #(methods i.ty go!"Stop" i.v)) (Val #()))
      {{ RET #(); True }})

instance isTickerI_persistent (tk : k8s_io.utils.clock.Ticker) :
    Persistent (isTickerI (GF := GF) tk) := by
  unfold isTickerI; infer_instance

/-- **A clock** (persistent; a `clock.WithTicker` or `clock.Clock` interface value). -/
def isClock (c : GoInterface) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜c = interface.ok i⌝ ∗
    {{ (True : IProp GF) }} (App (Val #(methods i.ty go!"Now" i.v)) (Val #()))
      {{ (t : time.Time), RET #t; True }} ∗
    (∀ d : time.Duration, {{ (True : IProp GF) }} (App (Val #(methods i.ty go!"NewTimer" i.v)) (Val #d))
      {{ (tm : k8s_io.utils.clock.Timer), RET #tm; isTimerI tm }}) ∗
    (∀ d : time.Duration, {{ ⌜0 < sint.Z d⌝ }} (App (Val #(methods i.ty go!"NewTicker" i.v)) (Val #d))
      {{ (tk : k8s_io.utils.clock.Ticker), RET #tk; isTickerI tk }}))

instance isClock_persistent (c : GoInterface) : Persistent (isClock (GF := GF) c) := by
  unfold isClock; infer_instance

/-! ### The waiting heap -/

/-- An entry `w` (a `*waitFor[T]`) of item `k` at index `i`: `data` read-only, `readyAt` and
`index` owned. -/
def wfAt (w : Loc) (k : K) (i : w64) : IProp GF :=
  iprop(structFieldRef (waitFor K) go!"data" w ↦□ k ∗
    (∃ t : time.Time, structFieldRef (waitFor K) go!"readyAt" w ↦ t) ∗
    structFieldRef (waitFor K) go!"index" w ↦ i)

/-- The heap's slice `s` holding the entries `ws`, each at its index, with the capacity. -/
def wqAt (s : GoSlice) (ws : List (Loc × K)) : IProp GF :=
  iprop(s ↦* (ws.map Prod.fst) ∗ ownSliceCap Loc s (DFrac.own 1) ∗
    [∗list] n ↦ x ∈ ws, wfAt (K := K) x.1 x.2 (W64 n))

/-- The heap at `pq` (a `*waitForPriorityQueue[T]`) holds the entries `ws`. -/
def wqHeap (pq : Loc) (ws : List (Loc × K)) : IProp GF :=
  iprop(∃ s : GoSlice, pq ↦ (s : waitForPriorityQueue K) ∗ wqAt (K := K) s ws)

/-- An element of the heap's `Push`/`Pop`: `x` the entry `a.1` of item `a.2`, owned, at any
index. -/
def wqElem (x : GoInterface) (a : Loc × K) : IProp GF :=
  iprop(⌜x = interface.mkOk (go.GoType.PointerType (waitFor.ty T)) #a.1⌝ ∗
    ∃ i : w64, wfAt (K := K) a.1 a.2 i)

/-- The waiting loop's map from item to entry holds exactly the heap's entries, no item twice. -/
def byDataOk (mm : GMap K Loc) (ws : List (Loc × K)) : Prop :=
  (ws.map Prod.snd).Nodup ∧ ∀ (k : K) (w : Loc), mm !! k = some w ↔ (w, k) ∈ ws

/-- `byDataOk` holds of a permutation of the entries. -/
theorem byDataOk_perm {mm : GMap K Loc} {ws ws' : List (Loc × K)} (h : byDataOk mm ws)
    (hp : ws'.Perm ws) : byDataOk mm ws' :=
  ⟨(hp.map Prod.snd).nodup_iff.2 h.1, fun k w => (h.2 k w).trans hp.mem_iff.symm⟩

/-- `byDataOk` of an entry `(w, k)` added under a new item `k`. -/
theorem byDataOk_insert {mm : GMap K Loc} {ws ws' : List (Loc × K)} (w : Loc) (k : K)
    (h : byDataOk mm ws) (hk : mm !! k = none) (hp : ws'.Perm (ws ++ [(w, k)])) :
    byDataOk (<[k := w]> mm) ws' := by
  obtain ⟨hnd, hmem⟩ := h
  have hkn : k ∉ ws.map Prod.snd := by
    intro hk'
    obtain ⟨⟨w', k'⟩, hin, he⟩ := List.mem_map.1 hk'
    have := (hmem k' w').2 hin
    simp only at he
    rw [he, hk] at this; cases this
  refine byDataOk_perm ⟨?_, fun k' w' => ?_⟩ hp
  · simp only [List.map_append, List.map_cons, List.map_nil]
    exact List.nodup_append.2 ⟨hnd, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩,
      fun a ha b hb e => by simp at hb; subst hb; subst e; exact hkn ha⟩
  · by_cases e : k = k'
    · subst e
      rw [GMap.lookup_insert]
      constructor
      · intro h; simp only [Option.some.injEq] at h; subst h
        exact List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))
      · intro h
        rcases List.mem_append.1 h with h | h
        · exact absurd (List.mem_map.2 ⟨_, h, rfl⟩) hkn
        · rw [List.mem_singleton] at h; cases h; rfl
    · rw [GMap.lookup_insert_ne _ _ e, hmem k' w']
      constructor
      · intro h; exact List.mem_append.2 (Or.inl h)
      · intro h
        rcases List.mem_append.1 h with h | h
        · exact h
        · rw [List.mem_singleton] at h; cases h; exact absurd rfl e

/-- `byDataOk` of the entries but the last, `(w, k)`, after `delete(m, k)`. -/
theorem byDataOk_delete {mm : GMap K Loc} {ws ws' : List (Loc × K)} (a : Loc × K)
    (h : byDataOk mm ws) (hp : (ws' ++ [a]).Perm ws) : byDataOk (GMap.delete a.2 mm) ws' := by
  obtain ⟨hnd, hmem⟩ := byDataOk_perm h hp
  simp only [List.map_append, List.map_cons, List.map_nil] at hnd
  obtain ⟨hnd', -, hdis⟩ := List.nodup_append.1 hnd
  refine ⟨hnd', fun k w => ?_⟩
  by_cases e : a.2 = k
  · subst e
    rw [GMap.lookup_delete]
    simp only [reduceCtorEq, false_iff]
    intro hin
    exact hdis _ (List.mem_map.2 ⟨_, hin, rfl⟩) _ (List.mem_singleton_self _) rfl
  · rw [GMap.lookup_delete_ne _ e, hmem k w]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | h)
      · exact h
      · subst h; exact absurd rfl e
    · exact Or.inl

/-- An entry sent on `waitingForAddCh`: a `*waitFor[T]` owned by its holder. -/
def entryOk (w : Loc) : IProp GF :=
  iprop(∃ wf : waitFor K, w ↦ wf)

/-! ### The delaying queue -/

/-- Retry metrics (persistent): `retry()` returns. -/
def isRetryMetrics (rm : retryMetrics) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜rm = interface.ok i⌝ ∗
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue }}
      (App (Val #(methods i.ty go!"retry" i.v)) (Val #()))
      {{ RET #(); True }})

instance isRetryMetrics_persistent (rm : retryMetrics) :
    Persistent (isRetryMetrics (GF := GF) rm) := by
  unfold isRetryMetrics; infer_instance

/-- **The delaying queue** (persistent): see the file header. -/
def isDelaying (q : Loc) (γ : DNames) : IProp GF :=
  iprop(∃ (tq : Loc) (c : GoInterface) (ch : Loc) (hb : k8s_io.utils.clock.Ticker) (wch : Loc)
      (rm : retryMetrics),
    "#Htq" ∷ structFieldRef (delayingType K) go!"TypedInterface" q ↦□
      (interface.mkOk (go.GoType.PointerType (Typed.ty T)) #tq : TypedInterface K) ∗
    "#Htyped" ∷ isTyped (K := K) tq γ.tq ∗
    "#Hclock" ∷ structFieldRef (delayingType K) go!"clock" q ↦□ c ∗
    "#Hc" ∷ isClock c ∗
    "#HstopCh" ∷ structFieldRef (delayingType K) go!"stopCh" q ↦□ ch ∗
    "#Hstop" ∷ ownBroadcastChan ch γ.stop (shutdownLb γ.tq) .Unknown ∗
    "#Honce" ∷ sync.isOnce (structFieldRef (delayingType K) go!"stopOnce" q)
      iprop(ownBroadcastChan ch γ.stop (shutdownLb γ.tq) .Pending ∗ shutdownToks γ.tq 1)
      (shutdownLb γ.tq) ∗
    "#Hhb" ∷ structFieldRef (delayingType K) go!"heartbeat" q ↦□ hb ∗
    "#Htk" ∷ isTickerI hb ∗
    "#Hwch" ∷ structFieldRef (delayingType K) go!"waitingForAddCh" q ↦□ wch ∗
    "#Hbag" ∷ isChanBag γ.wch wch (V := Loc) (entryOk (K := K)) ∗
    "#Hmetrics" ∷ structFieldRef (delayingType K) go!"metrics" q ↦□ rm ∗
    "#Hrm" ∷ isRetryMetrics rm)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
instance isDelaying_persistent (q : Loc) (γ : DNames) :
    Persistent (isDelaying (GF := GF) (K := K) q γ) := by
  unfold isDelaying; simp only [named]; infer_instance

/-- **The rate-limiting queue** (persistent): a `*rateLimitingType[T]` over the delaying queue
`dq` and a rate limiter whose `When` satisfies `P`. -/
def isRateLimitingQueue (q : Loc) (γ : DNames) (P : time.Duration → Prop) : IProp GF :=
  iprop(∃ (dq : Loc) (rl : TypedRateLimiter K),
    structFieldRef (rateLimitingType K) go!"TypedDelayingInterface" q ↦□
      (interface.mkOk (go.GoType.PointerType (delayingType.ty T)) #dq : TypedDelayingInterface K) ∗
    isDelaying (K := K) dq γ ∗
    structFieldRef (rateLimitingType K) go!"rateLimiter" q ↦□ rl ∗
    isRateLimiter (K := K) rl P)

instance isRateLimitingQueue_persistent (q : Loc) (γ : DNames) (P : time.Duration → Prop) :
    Persistent (isRateLimitingQueue (GF := GF) (K := K) q γ P) := by
  unfold isRateLimitingQueue; infer_instance

end defs

/-! ### `Time`'s methods through a pointer, at any fraction -/

section time
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [time_sem : time.Assumptions]

/-- `(*Time).After` on `*l`: some `bool`. -/
theorem Time.wp_ptr_After_dq (l : Loc) (t u : time.Time) (dq : DFrac) :
    {{ (l ↦{dq} t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"After")) (Val #u))
    {{ (b : Bool), RET #b; l ↦{dq} t }} := by
  wp_start as Hl
  wp_auto
  wp_apply time.Time.wp_After as %b -
  iapply HΦ $$ Hl

/-- `(*Time).Before` on `*l`: some `bool`. -/
theorem Time.wp_ptr_Before_dq' (l : Loc) (t u : time.Time) (dq : DFrac) :
    {{ (l ↦{dq} t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"Before")) (Val #u))
    {{ (b : Bool), RET #b; l ↦{dq} t }} := by
  wp_start as Hl
  wp_auto
  wp_apply time.Time.wp_Before as %b -
  iapply HΦ $$ Hl

/-- `(*Time).Sub` on `*l`: some duration. -/
theorem Time.wp_ptr_Sub_dq (l : Loc) (t u : time.Time) (dq : DFrac) :
    {{ (l ↦{dq} t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"Sub")) (Val #u))
    {{ (d : w64), RET #d; l ↦{dq} t }} := by
  wp_start as Hl
  wp_auto
  wp_apply time.Time.wp_Sub as %d -
  iapply HΦ $$ Hl

end time

end workqueue
end EtcdGrove
end Perennial
