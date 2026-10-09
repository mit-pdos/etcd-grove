/-
etcd's cache `Cache` (`cache/cache.go`, `cache/predicate.go`): the vocabulary of the
request-side helpers' specs (`Spec/{ExactKey,FromKey,Range,KeyPredForRange}.lean`,
`Spec/Cache__validate*.lean`, `Spec/Cache__{Ready,WaitReady,RequestProgress}.lean`) and of
the `clientv3` functions they call (`Spec/Op__*.lean`, `Spec/GetPrefixRangeEnd.lean`,
`Spec/getPrefix.lean`). Lean-first (no Rocq counterpart).

**Keys.** A Go `[]byte` key is modelled by its contents, a `GoString` (`List w8`, as Go's
`string([]byte)` conversion is): `sl ↦*{dq} k`. `bytes.Equal`/`bytes.Compare` are Go's `==`
and `<` on the strings (`bytes.wp_Equal`, `bytes.wp_Compare`), so a key predicate is a
function `GoString → Bool` in terms of `go.GoStringLt`, the order of the store's maps
(`InvStore.lean`). `keyPredForRange start end` is the predicate `KeyPredForRange` builds;
it is `kvRange`'s membership test (`mem_kvRange`), so `Get`'s range and `Watch`'s filter
select the same keys.

**Ranges.** `validRange prefix start end` is `Cache.validateRange`: the range must lie
within the cache's prefix (`prefixRangeEnd`, `clientv3.GetPrefixRangeEnd`, is the least key
above every key with the prefix; `[0]` if there is none).

**`clientv3.Op`.** An `Op` is a struct value; `OpModel` is what the cache's helpers read of
it through its getters, `opAt op o` relates them (the range end is a read-only byte slice).

**The `Cache`'s fields.** `isCacheFields c cf γr γd cap` is the `Cache` predicate: every
field (but the wait group's state, under `cacheWgInv`), read-only, with the persistent
predicates of the components (`newCache` establishes it, `InvNew.lean`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvDemux
public import Proof.go_etcd_io.etcd.cache.v3.InvReady
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcd

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## Key predicates -/

/-- `ExactKey(key)`: `k == key`. -/
def exactKeyPred (key : GoString) (k : GoString) : Bool := decide (k = key)

/-- `FromKey(start)`: `k >= start`. -/
def fromKeyPred (start : GoString) (k : GoString) : Bool := !decide (go.GoStringLt k start)

/-- `Range(start, end)`: `start <= k < end`. -/
def rangePred (start end_ : GoString) (k : GoString) : Bool :=
  !decide (go.GoStringLt k start) && decide (go.GoStringLt k end_)

/-- `KeyPredForRange(start, end)`: the key `start` alone if `end` is empty, the keys from
`start` on if `end` is `"\x00"`, the keys in `[start, end)` otherwise. -/
def keyPredForRange (start end_ : GoString) : GoString → Bool :=
  if end_ = [] then exactKeyPred start
  else if end_ = [W8 0] then fromKeyPred start
  else rangePred start end_

/-- `kvRange` (`snapshot.Range`, the store's `Get`) filters by `keyPredForRange`. -/
theorem kvRange_eq_filter (start end_ : GoString) (m : KvMap) :
    kvRange start end_ m = m.filter (fun e => keyPredForRange start end_ e.1) := by
  unfold kvRange keyPredForRange exactKeyPred fromKeyPred rangePred
  split <;> (try split) <;> rfl

/-- An entry is in `kvRange start end m` iff it is in `m` and its key satisfies
`keyPredForRange start end`. -/
theorem mem_kvRange (start end_ : GoString) (m : KvMap) (e : KvEntry) :
    e ∈ kvRange start end_ m ↔ e ∈ m ∧ keyPredForRange start end_ e.1 = true := by
  rw [kvRange_eq_filter, List.mem_filter]

/-! ## `bytes.Compare` -/

theorem goStringLt_asymm {a b : GoString} (h : go.GoStringLt a b) : ¬ go.GoStringLt b a :=
  fun h' => goStringLt_irrefl a (goStringLt_trans h h')

theorem compareResult_lt (a b : GoString) :
    sint.Z (bytes.compareResult a b) < 0 ↔ go.GoStringLt a b := by
  unfold bytes.compareResult
  by_cases h : go.GoStringLt a b
  · simp only [h, ↓reduceIte, iff_true]; decide
  · simp only [h, ↓reduceIte, iff_false]
    split <;> decide

theorem compareResult_ge (a b : GoString) :
    0 ≤ sint.Z (bytes.compareResult a b) ↔ ¬ go.GoStringLt a b := by
  rw [← compareResult_lt]; omega

theorem compareResult_gt (a b : GoString) :
    0 < sint.Z (bytes.compareResult a b) ↔ go.GoStringLt b a := by
  unfold bytes.compareResult
  by_cases h : go.GoStringLt a b
  · simp only [h, ↓reduceIte]
    exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' (goStringLt_asymm h)⟩
  · simp only [h, ↓reduceIte]
    by_cases he : a = b
    · subst he; simp only [↓reduceIte]
      exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' (goStringLt_irrefl a)⟩
    · simp only [he, ↓reduceIte]
      refine ⟨fun _ => ?_, fun _ => by decide⟩
      exact Classical.byContradiction fun h' => he (goStringLt_eq_of_not_lt h h')

theorem compareResult_le (a b : GoString) :
    sint.Z (bytes.compareResult a b) ≤ 0 ↔ ¬ go.GoStringLt b a := by
  rw [← compareResult_gt]; omega

/-! ## Ranges -/

/-- `Cache.validateRange(start, end)` on a cache with prefix `pfx`: a single key (`end`
empty) must be in the prefix's range `[pfx, prefixRangeEnd pfx)`; a "from key" range (`end`
is `"\x00"`) needs the root cache (`pfx` empty); a range `[start, end)` must be non-empty and
within `[pfx, prefixRangeEnd pfx]`. The root cache accepts every key and every non-empty
range. -/
def validRange (pfx start end_ : GoString) : Bool :=
  if end_ = [] then
    decide (pfx = []) ||
      (!decide (go.GoStringLt start pfx) && decide (go.GoStringLt start (prefixRangeEnd pfx)))
  else if end_ = [W8 0] then decide (pfx = [])
  else
    decide (go.GoStringLt start end_) &&
      (decide (pfx = []) ||
        (!decide (go.GoStringLt start pfx) && !decide (go.GoStringLt (prefixRangeEnd pfx) end_)))

/-! ## The `Cache`'s fields -/

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&c.prefix` -/
abbrev cachePrefixAddr (c : Loc) : Loc := structFieldRef Cache go!"prefix" c
/-- `&c.cfg` -/
abbrev cacheCfgAddr (c : Loc) : Loc := structFieldRef Cache go!"cfg" c
/-- `&c.ready` -/
abbrev cacheReadyAddr (c : Loc) : Loc := structFieldRef Cache go!"ready" c
/-- `&c.demux` -/
abbrev cacheDemuxAddr (c : Loc) : Loc := structFieldRef Cache go!"demux" c
/-- `&c.store` -/
abbrev cacheStoreAddr (c : Loc) : Loc := structFieldRef Cache go!"store" c
/-- `&c.kv` -/
abbrev cacheKvAddr (c : Loc) : Loc := structFieldRef Cache go!"kv" c
/-- `&c.progressRequestor` -/
abbrev cachePrAddr (c : Loc) : Loc := structFieldRef Cache go!"progressRequestor" c
/-- `&p.mux` -/
abbrev prMuxAddr (p : Loc) : Loc := structFieldRef conditionalProgressRequestor go!"mux" p

end addrs

/-- The values of the `Cache` fields `isCacheFields` covers (fixed by `newCache`), with the
store's ghost names and history capacity. -/
structure CacheFields [FfiSyntax] where
  pfx : GoString
  cfg : Config
  ready : Loc
  demux : Loc
  store : Loc
  /-- the store's ghost names -/
  γs : StoreNames
  /-- the store's history capacity -/
  scap : Nat
  /-- the `clientv3.KV` interface value -/
  kv : GoInterfaceOk
  /-- the `*conditionalProgressRequestor` in the `progressRequestor` interface -/
  pr : Loc
  /-- the `clientv3.Watcher` interface value -/
  watcher : GoInterfaceOk
  /-- the internal context (`internalCtx`) -/
  ictx : GoInterfaceOk
  /-- the `Clock` interface value -/
  clock : GoInterfaceOk
  /-- the wait group's ghost names (Perennial's `isWaitGroup`) -/
  γwg : sync.WaitGroupNames
  /-- the wait group's budget tokens (`cacheWgInv`) -/
  γwb : GName
  /-- the wait group's running tokens (`cacheWgInv`) -/
  γwr : GName
  /-- the cancel function of the internal context (`stop`) -/
  stop : GoFunc
  /-- the "open" token (`cacheOpen`): `Watch` needs a fraction, `Close` all of it -/
  γop : GName

/-! ## The watch loop and `Cache.Watch`: the cache's other fields -/

section addrs2
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&c.watcher` -/
abbrev cacheWatcherAddr (c : Loc) : Loc := structFieldRef Cache go!"watcher" c
/-- `&c.internalCtx` -/
abbrev cacheICtxAddr (c : Loc) : Loc := structFieldRef Cache go!"internalCtx" c
/-- `&c.clock` -/
abbrev cacheClockAddr (c : Loc) : Loc := structFieldRef Cache go!"clock" c
/-- `&c.waitGroup` -/
abbrev cacheWgAddr (c : Loc) : Loc := structFieldRef Cache go!"waitGroup" c
/-- `&c.stop` -/
abbrev cacheStopAddr (c : Loc) : Loc := structFieldRef Cache go!"stop" c
/-- `&r.timer` of a `*realTimer`. -/
abbrev realTimerTimerAddr (r : Loc) : Loc := structFieldRef realTimer go!"timer" r

end addrs2

/-- The namespace of the `Cache`'s wait group (Perennial's `isWaitGroup`). -/
def cacheWgWGN : Namespace := nroot.@"cacheWaitGroup"

/-- The namespace of the `Cache`'s wait-group counter invariant (`cacheWgInv`). -/
def cacheWgN : Namespace := nroot.@"cacheWgCounter"

/-- The goroutines the cache may have running at once (the wait group's counter is an `int32`
that must not overflow). -/
def cacheWgBudget : Nat := 2 ^ 31 - 1

section clock
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `t` is a `Timer` (`cache/clock.go`; the trust boundary for the clock, a definition like
`isLocker`, instantiated by `realTimer`: `realClock.NewTimer`'s spec): `Chan()` returns a channel from
which a receive yields some time (a bag of times, `isChanBag`); `Reset(d)` and `Stop()` return a
bool, with no logical effect. -/
def isTimer (t : GoInterfaceOk) : IProp GF :=
  iprop({{ True }} (App (Val #(methods t.ty go!"Chan" t.v)) (Val #()))
      {{ (ch : Loc) (γ : ChanNames), RET #ch;
          isChanBag γ ch (V := time.Time) (fun _ => iprop(True)) }} ∗
    (∀ d : time.Duration, {{ True }} (App (Val #(methods t.ty go!"Reset" t.v)) (Val #d))
      {{ (b : Bool), RET #b; True }}) ∗
    {{ True }} (App (Val #(methods t.ty go!"Stop" t.v)) (Val #()))
      {{ (b : Bool), RET #b; True }})

instance isTimer_persistent (t : GoInterfaceOk) : Persistent (isTimer (GF := GF) t) := by
  unfold isTimer; infer_instance

/-- `clk` is a `Clock`: `NewTimer(d)` returns a timer (`isTimer`). -/
def isClock (clk : GoInterfaceOk) : IProp GF :=
  iprop(∀ d : time.Duration, {{ True }} (App (Val #(methods clk.ty go!"NewTimer" clk.v)) (Val #d))
    {{ (t : GoInterfaceOk), RET #(GoInterface.ok t); isTimer t }})

instance isClock_persistent (clk : GoInterfaceOk) : Persistent (isClock (GF := GF) clk) := by
  unfold isClock; infer_instance

/-- `r` is a `*realTimer` (`cache/clock.go`, persistent): its `timer` is, for good, a `*time.Timer`
made by `time.NewTimer` (Perennial's `time.isTimer`, the trust boundary of the timers). -/
def isRealTimer (r : Loc) : IProp GF :=
  iprop(∃ (t ch : Loc) (γ : ChanNames), realTimerTimerAddr r ↦□ t ∗ time.isTimer t ch γ)

instance isRealTimer_persistent (r : Loc) : Persistent (isRealTimer (GF := GF) r) := by
  unfold isRealTimer; infer_instance

end clock

/-! ## The watch loop: the writer's position and the store watcher's -/

/-- Nothing under the prefix changed between the stream's last batch (`last`; `base` for an
empty stream) and `cursor`, or `cursor` is not past it: a progress step from at most `last` to
`cursor`. What lets the writer certify the next batch of its watch, which starts at `cursor`,
from the stream's last batch (`respCert`). -/
def TailOk (pfx : GoString) (last : Int) (cursor : w64) : Prop :=
  sint.Z cursor ≤ last ∨ ∃ q : w64, sint.Z q ≤ last ∧ EtcdStep q cursor pfx []

/-- The writer's invariant across watches: once `maxRev` is set, nothing changed between the last
batch and `maxRev` (`Init` continues a stream at `maxRev + 1`). -/
def WriterOk (pfx : GoString) (c : DemuxCore) : Prop :=
  c.maxRev ≠ W64 0 → TailOk pfx c.lastRev c.maxRev

/-- A watch at `cursor` continues the demux's stream: initialized, its base at or below
`cursor`, and nothing changed between the last batch and `cursor`. -/
def CursorOk (pfx : GoString) (c : DemuxCore) (cursor : w64) : Prop :=
  c.minRev ≠ W64 0 ∧ c.base ≤ sint.Z cursor ∧ TailOk pfx c.lastRev cursor

/-- After `Init(rev)` the stream continues a watch at `rev - 1`, and the writer's invariant
holds. -/
theorem initCore_ok (pfx : GoString) (cap : Nat) (c : DemuxCore) (rev : w64)
    (hinv : DemuxInv cap c) (hw : WriterOk pfx c) (hrev : 0 < sint.Z rev) :
    CursorOk pfx (initCore c rev).1 (rev - W64 1) ∧ WriterOk pfx (initCore c rev).1 := by
  have hr1 : sint.Z (rev - W64 1) = sint.Z rev - 1 := by word
  have hne : rev ≠ W64 0 := by intro h; subst h; simp at hrev
  unfold initCore
  rw [ite_eq_right hne]
  by_cases h0 : c.minRev = W64 0
  · rw [ite_eq_left h0]
    obtain ⟨hs, hm⟩ := hinv.uninit h0
    refine ⟨⟨hne, ?_, Or.inl ?_⟩, fun h => absurd hm h⟩
    · show sint.Z rev - 1 ≤ sint.Z (rev - W64 1); omega
    · unfold DemuxCore.lastRev; rw [hs]; show sint.Z (rev - W64 1) ≤ sint.Z rev - 1; omega
  rw [ite_eq_right h0]
  have hinit : CursorOk pfx { DemuxCore.init with minRev := rev, base := sint.Z rev - 1 }
      (rev - W64 1) ∧ WriterOk pfx { DemuxCore.init with minRev := rev, base := sint.Z rev - 1 } := by
    refine ⟨⟨hne, ?_, Or.inl ?_⟩, fun h => absurd rfl h⟩
    · show sint.Z rev - 1 ≤ sint.Z (rev - W64 1); omega
    · show sint.Z (rev - W64 1) ≤ sint.Z rev - 1; omega
  by_cases h2 : c.maxRev = W64 0
  · rw [ite_eq_left h2]; exact hinit
  rw [ite_eq_right h2]
  by_cases h3 : rev = c.maxRev + W64 1
  · rw [ite_eq_left h3]
    have hk : rev - W64 1 = c.maxRev := by rw [h3]; bv_omega
    rw [hk]
    exact ⟨⟨h0, hinv.base_maxRev h2, hw h2⟩, hw⟩
  · rw [ite_eq_right h3]; exact hinit

/-- The revision of the last event of a log of responses, `dflt` if it has none: where the store
watcher's consumer is in the stream. -/
def lastEvRevOr (L : List RespModel) (dflt : Int) : Int :=
  match (eventsOf L).getLast? with
  | some e => sint.Z e.rev
  | none => dflt

/-- The ghost names of the channel `Cache.Watch` returns: the channel's (an SPSC channel:
`Watch`'s goroutine produces, the caller consumes) and the log of the responses sent on it
(`fwd`, a monotone list). -/
structure CacheWatchNames where
  spsc : SpscNames
  fwd : GName

section prdefs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- The lock invariant of a `conditionalProgressRequestor`'s `mux`: the waiter count and the
stopped flag (`run`'s loop reads both under the lock, its goroutine sets `stopped`). -/
def prLockInv (p : Loc) : IProp GF :=
  iprop(∃ (w : w32) (b : Bool),
    structFieldRef conditionalProgressRequestor go!"waiting" p ↦ w ∗
    structFieldRef conditionalProgressRequestor go!"stopped" p ↦ b)

/-- `p` is a `*conditionalProgressRequestor` (persistent): its `mux` guards `prLockInv`, its
`cond` is a condition variable on `&p.mux` (`sync.NewCond(&p.mux)`). `add`/`remove` change the
waiter count under the lock. -/
def isProgressRequestor (p : Loc) : IProp GF :=
  iprop(∃ cp : Loc,
    structFieldRef conditionalProgressRequestor go!"cond" p ↦□ cp ∗
    sync.isCond cp (interface.mk (go.GoType.PointerType sync.Mutex.ty) #(prMuxAddr p)) ∗
    sync.isMutex (prMuxAddr p) (prLockInv p))

instance isProgressRequestor_persistent (p : Loc) :
    Persistent (isProgressRequestor (GF := GF) p) := by
  unfold isProgressRequestor; infer_instance

/-- The fields of a `*conditionalProgressRequestor` that only `run` reads (persistent): the
`notifier` (`n`), `requestInterval` (`ri`) and `clock` (`clk`), fixed by
`newConditionalProgressRequestor`. -/
def isPrRun (p : Loc) (n clk : GoInterface) (ri : time.Duration) : IProp GF :=
  iprop(structFieldRef conditionalProgressRequestor go!"notifier" p ↦□ n ∗
    structFieldRef conditionalProgressRequestor go!"requestInterval" p ↦□ ri ∗
    structFieldRef conditionalProgressRequestor go!"clock" p ↦□ clk)

instance isPrRun_persistent (p : Loc) (n clk : GoInterface) (ri : time.Duration) :
    Persistent (isPrRun (GF := GF) p n clk ri) := by
  unfold isPrRun; infer_instance

end prdefs

/-! ## The watch loop and `Cache.Watch`: the cache's predicates -/

section watchdefs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- The "open" token of the cache, a fraction `q` of it: `Watch` (which may `Add(1)` to the wait
group from zero) needs a fraction, `Close` (which waits on it) all of it, so the two never run at
once (Perennial's `WaitGroup` spec forbids an `Add` from zero while a waiter is registered). -/
def cacheOpen (cf : CacheFields) (q : Qp) : IProp GF := ghostVar cf.γop q ()

/-- The `Cache`'s wait group's counter (an invariant): `ctr` goroutines running, each with a
running token (`γwr`, for its `Done`) and each having spent a budget token (`γwb`, of which there
are `cacheWgBudget` in all: the counter cannot overflow); and at most one waiter (`Close`), which
while registered has deposited the whole "open" token (`cacheOpen`), so that no `Watch` adds to
the wait group meanwhile. -/
def cacheWgInv (cf : CacheFields) : IProp GF :=
  iprop(∃ (ctr : w32) (w : Nat), sync.ownWaitGroup cf.γwg ctr ∗ sync.ownWaitGroupWaiters cf.γwg w ∗
    ownTokAuth cf.γwr (sint.nat ctr) ∗ ownToks cf.γwb (sint.nat ctr) ∗
    ownTokAuth cf.γwb cacheWgBudget ∗ ⌜0 ≤ sint.Z ctr⌝ ∗
    (⌜w = 0⌝ ∨ (⌜w = 1⌝ ∗ cacheOpen cf 1)))

instance cacheWgInv_timeless (cf : CacheFields) : Timeless (cacheWgInv (GF := GF) cf) := by
  unfold cacheWgInv cacheOpen; infer_instance

/-- The right to start one goroutine on the cache's wait group (`Add(1)`): a budget token. -/
def cacheWgSlot (cf : CacheFields) : IProp GF := ownToks cf.γwb 1

/-- A goroutine started on the cache's wait group, before its `Done()`. -/
def cacheWgRunning (cf : CacheFields) : IProp GF := ownToks cf.γwr 1

theorem cacheWg_mask : (↑cacheWgWGN : CoPset) ⊆ ⊤ \ ↑cacheWgN :=
  sync.wg_mask_ndot_ne nroot "cacheWaitGroup" "cacheWgCounter" (by decide)

/-- The "open" token's fractions add up to at most `1`. -/
theorem cacheOpen_excl (cf : CacheFields) (q : Qp) :
    cacheOpen (GF := GF) cf q ∗ cacheOpen cf 1 ⊢ False := by
  unfold cacheOpen
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives % ⟨Hv, -⟩
  exfalso
  have h1 := Qp.le_iff.1 Hv
  have h2 := q.2
  simp only [Qp.val_add, Qp.val_one] at h1
  grind

/-- `c.waitGroup.Add(1)`, spending a goroutine slot (`cacheWgSlot`) for a running token, with a
fraction of the "open" token (no `Close` waits meanwhile). -/
theorem wp_cacheWg_Add (c : Loc) (cf : CacheFields) (q : Qp) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (cacheWgAddr c) cf.γwg cacheWgWGN ∗
        inv cacheWgN (cacheWgInv cf) ∗ cacheWgSlot cf ∗ cacheOpen cf q }}
      (App (Val (cacheWgAddr c @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); cacheWgRunning cf ∗ cacheOpen cf q }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Hslot, Hopen⟩ HΦ
  iapply sync.WaitGroup.wp_Add (cacheWgAddr c) (W64 1) cf.γwg cacheWgWGN $$ [] [Hslot Hopen HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro cacheWg_mask
  iintro Hmask
  inext
  iunfold cacheWgInv at Hi
  icases Hi with ⟨%ctr, %wn, Hwgo, Hwt, Hrun, Hbud, Hbauth, %Hctr, Hwn⟩
  icases Hwn with (%Hw0 | ⟨-, Hop1⟩)
  rotate_left
  · iexfalso
    iapply cacheOpen_excl cf q $$ [$Hopen $Hop1]
  subst Hw0
  unfold cacheWgSlot
  ihave Hbud' := ownToks_add_2 1 (sint.nat ctr) cf.γwb $$ [Hbud Hslot]
  · iframe
  icombine Hbauth Hbud' gives %Hle
  iexists ctr
  iframe Hwgo
  have h1 : sint.Z (W32 (sint.Z (W64 1))) = 1 := by decide
  have hc : ((sint.nat ctr : Nat) : Int) = sint.Z ctr := Int.toNat_of_nonneg Hctr
  have hle : sint.Z ctr + 1 ≤ 2 ^ 31 - 1 := by
    unfold cacheWgBudget at Hle; omega
  have hn : sint.nat (ctr + W32 (sint.Z (W64 1))) = sint.nat ctr + 1 := by
    rw [show W32 (sint.Z (W64 1)) = W32 1 from rfl]; word
  isplitr
  · ipureintro; rw [h1]; omega
  iright
  iframe Hwt
  iintro Hwt Hwgo
  imod Hmask with -
  imod ownTokAuth_S cf.γwr (sint.nat ctr) $$ Hrun with ⟨Hrun, Hrtok⟩
  imod Hclose $$ [Hwgo Hwt Hrun Hbud' Hbauth] with -
  · inext
    unfold cacheWgInv
    iexists ctr + W32 (sint.Z (W64 1)), 0
    rw [hn]
    iframe
    isplitr
    · ipureintro
      have : sint.Z (ctr + W32 (sint.Z (W64 1))) = sint.Z ctr + 1 := by
        rw [show W32 (sint.Z (W64 1)) = W32 1 from rfl]; word
      omega
    ileft; ipureintro; rfl
  imodintro
  iapply HΦ
  unfold cacheWgRunning
  iframe

/-- `c.waitGroup.Done()`, with a running token. -/
theorem wp_cacheWg_Done (c : Loc) (cf : CacheFields) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (cacheWgAddr c) cf.γwg cacheWgWGN ∗
        inv cacheWgN (cacheWgInv cf) ∗ cacheWgRunning cf }}
      (App (Val (cacheWgAddr c @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Hrtok⟩ HΦ
  iapply sync.WaitGroup.wp_Done (cacheWgAddr c) cf.γwg cacheWgWGN $$ [] [Hrtok HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro cacheWg_mask
  iintro Hmask
  inext
  iunfold cacheWgInv at Hi
  icases Hi with ⟨%ctr, %wn, Hwgo, Hwt, Hrun, Hbud, Hbauth, %Hctr, Hwn⟩
  unfold cacheWgRunning
  icombine Hrun Hrtok gives %Hle
  have hc : ((sint.nat ctr : Nat) : Int) = sint.Z ctr := Int.toNat_of_nonneg Hctr
  have h1 : 1 ≤ sint.Z ctr := by omega
  have hn : sint.nat (ctr - W32 1) = sint.nat ctr - 1 := by word
  have hz : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by word
  have hb : sint.Z ctr < 2 ^ 31 := by word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; omega
  iintro Hwgo
  imod Hmask with -
  rw [show sint.nat ctr = (sint.nat ctr - 1) + 1 by omega]
  imod ownTokAuth_delete_S cf.γwr (sint.nat ctr - 1) $$ Hrun Hrtok with Hrun
  icases ownToks_add_1 1 (sint.nat ctr - 1) cf.γwb $$ Hbud with ⟨Hbud, -⟩
  imod Hclose $$ [Hwgo Hwt Hrun Hbud Hbauth Hwn] with -
  · inext
    unfold cacheWgInv
    iexists ctr - W32 1, wn
    rw [hn]
    iframe
    ipureintro
    omega
  imodintro
  iapply HΦ
  itrivial

/-- The demux's writer for the cache (`etcdStepCert`), with its invariant across watches. -/
def cacheWriter (cf : CacheFields) (γd : DemuxNames) (cap : Nat) (c : DemuxCore) : IProp GF :=
  iprop(demuxWriter cf.demux γd cap (etcdStepCert cf.pfx) c ∗ ⌜WriterOk cf.pfx c⌝)

/-- What a log `L` of responses on `Cache.Watch`'s channel is: a log the watcher's producer had,
with its delivery facts and certificates (`demuxPubBody … none`); or such a log closed by a
compaction at `n` followed by the compaction's cancel response; or the single cancel response of
a request `validateWatch` rejected. -/
def cacheWatchLog (C : DemuxCert GF) (pred : Option (GoString → Bool)) (sr : w64)
    (L : List RespModel) : IProp GF :=
  iprop(demuxPubBody C pred sr none L ∨
    (∃ (L0 : List RespModel) (n : w64), ⌜L = L0 ++ [cancelModel n]⌝ ∗
      demuxPubBody C pred sr (some (some n)) L0) ∨
    ⌜∃ r, L = [r] ∧ r.canceled = true ∧ r.events = []⌝)

instance cacheWatchLog_persistent (C : DemuxCert GF) (pred : Option (GoString → Bool)) (sr : w64)
    (L : List RespModel) : Persistent (cacheWatchLog C pred sr L) := by
  unfold cacheWatchLog; infer_instance

/-- The `i`-th response `v` on `Cache.Watch`'s channel: modelled by `r`, the `i`-th of a log `L`
(of the monotone log `fwd`) that is a `cacheWatchLog`. -/
def cacheWatchElem (γ : CacheWatchNames) (C : DemuxCert GF) (pred : Option (GoString → Bool))
    (sr : w64) (i : Int) (v : go_etcd_io.etcd.client.v3.WatchResponse) : IProp GF :=
  iprop(∃ (L : List RespModel) (r : RespModel), respAt v r ∗
    ⌜L.length = i.toNat + 1 ∧ L[i.toNat]? = some r⌝ ∗ monoListLbOwn γ.fwd L ∗
    cacheWatchLog C pred sr L)

/-- `rc` is a channel `Cache.Watch` returned (persistent), for certificates `C`, key filter
`pred` and start revision `sr`. -/
def isCacheWatchChan (rc : Loc) (γ : CacheWatchNames) (C : DemuxCert GF)
    (pred : Option (GoString → Bool)) (sr : w64) : IProp GF :=
  isSpsc γ.spsc rc (cacheWatchElem γ C pred sr) (fun _ => iprop(True))

instance isCacheWatchChan_persistent (rc : Loc) (γ : CacheWatchNames) (C : DemuxCert GF)
    (pred : Option (GoString → Bool)) (sr : w64) :
    Persistent (isCacheWatchChan (GF := GF) rc γ C pred sr) := by
  unfold isCacheWatchChan; infer_instance

/-- The consumer of `Cache.Watch`'s channel: it has received the responses `rs`, a
`cacheWatchLog` (when not empty). -/
def cacheWatchConsumer (γ : CacheWatchNames) (C : DemuxCert GF) (pred : Option (GoString → Bool))
    (sr : w64) (rs : List RespModel) : IProp GF :=
  iprop(∃ vs : List go_etcd_io.etcd.client.v3.WatchResponse, spscConsumer γ.spsc vs ∗
    ⌜vs.length = rs.length⌝ ∗ monoListLbOwn γ.fwd rs ∗ (⌜rs = []⌝ ∨ cacheWatchLog C pred sr rs))

/-- What `Cache.Watch`'s caller needs: one of the demux's tokens (the watch's goroutine registers,
sends progress notifications and unregisters with it) and a goroutine slot of the cache's wait
group (both kept by the goroutine). -/
def cacheWatchSlot (cf : CacheFields) (γd : DemuxNames) (cap : Nat) : IProp GF :=
  iprop(demuxHandle cf.demux γd cap (etcdStepCert cf.pfx) ∗ cacheWgSlot cf)

/-- A log published by the demux with nothing in it (`newWatcher`'s premise, for the watcher
`Watch` registers with start `sr`). -/
theorem demuxPubBody_nil (C : DemuxCert GF) (pred : Option (GoString → Bool)) (sr : w64) :
    ⊢ demuxPubBody C pred sr none [] := by
  unfold demuxPubBody
  iexists sr, View.mk [] (W64 0) sr .active, sint.Z sr - 1
  isplitr
  · ipureintro
    refine ⟨Or.inr rfl, ?_, Or.inr (by omega), fun m h => by cases h⟩
    exact Delivered.init pred sr _ ⟨(fun _ h => by cases h), List.Pairwise.nil,
      (fun _ h => by cases h)⟩ (fun _ h => by cases h) rfl (fun m h => by cases h)
  have h0 : streamRange sr (View.mk [] (W64 0) sr .active).n
      (View.mk [] (W64 0) sr .active).stream = [] := rfl
  rw [h0]
  isplitr
  · iapply certChain_nil
  · imodintro; iapply C.prog_zero

/-- **Receiving** on `Cache.Watch`'s channel: with `ok`, the next response, the received log
(`rs ++ [r]`) still a `cacheWatchLog`; without, the channel was closed. -/
theorem wp_cacheWatch_receive (rc : Loc) (γ : CacheWatchNames) (C : DemuxCert GF)
    (pred : Option (GoString → Bool)) (sr : w64) (rs : List RespModel) :
    {{ isCacheWatchChan rc γ C pred sr ∗ cacheWatchConsumer γ C pred sr rs }}
      (App (Val (chan.receive go_etcd_io.etcd.client.v3.WatchResponse.ty)) (Val #rc))
    {{ (v : go_etcd_io.etcd.client.v3.WatchResponse) (ok : Bool), RET (PairV #v #ok);
        if ok then iprop(∃ r : RespModel, respAt v r ∗ cacheWatchConsumer γ C pred sr (rs ++ [r]))
        else iprop(⌜v = zero_val go_etcd_io.etcd.client.v3.WatchResponse⌝) }} := by
  iintro %Φ ⟨#Hch, Hcons⟩ HΦ
  unfold cacheWatchConsumer
  icases Hcons with ⟨%vs, Hcons, %Hlen, #Hlb, #Hlog⟩
  unfold isCacheWatchChan
  iapply wp_spsc_receive γ.spsc rc (cacheWatchElem γ C pred sr) (fun _ => iprop(True)) vs
    $$ [$Hch $Hcons]
  inext
  iintro %v %ok H
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases H with ⟨-, %Hv⟩
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; exact Hv
  · simp only [↓reduceIte]
    icases H with ⟨HP, Hcons⟩
    unfold cacheWatchElem
    icases HP with ⟨%L, %r, #Hr, %HL, #HlbL, #HlogL⟩
    have hi : ((vs.length : Int)).toNat = rs.length := by rw [Hlen]; simp
    rw [hi] at HL
    ihave %Hpre := mono_list_lb_valid γ.fwd rs L $$ Hlb HlbL
    have hL : L = rs ++ [r] := by
      rcases Hpre with ⟨t, ht⟩ | hp
      · subst ht
        have ht1 : t.length = 1 := by simp at HL; omega
        obtain ⟨x, rfl⟩ : ∃ x, t = [x] := by
          cases t with
          | nil => simp at ht1
          | cons x t' => cases t' with
            | nil => exact ⟨x, rfl⟩
            | cons _ _ => simp at ht1
        have : (rs ++ [x])[rs.length]? = some x := by simp
        rw [HL.2] at this
        cases this; rfl
      · have := hp.length_le; omega
    subst hL
    iapply HΦ
    simp only [↓reduceIte]
    iexists r
    iframe Hr
    iexists vs ++ [v]
    iframe Hcons
    iframe HlbL
    isplitr
    · ipureintro; simp [Hlen]
    iright; iexact HlogL

/-- **The `Watch` delivery theorem** (for one log, `Cache.Watch`'s certificates and key filter): the
events of a log the demux delivered to a watch on `[key, rangeEnd)` from `sr` are exactly the events
of etcd's batches `bs` whose keys the filter accepts, in order (no gap, no duplicate); the log is
in order (`SentOrdered`: events increasing from response to response, progress notifications at or
above everything before and below everything after); `bs` are batches of one revision each,
increasing; each batch is certified by etcd's step from at most the previous batch's revision
(`certChain (etcdStepCert pfx) p₀ bs`: its events are etcd's, and nothing under the prefix
changed in between), the first one from `p₀`; and for a start `sr ≠ 0`, `p₀ < sr ≤` every batch's
revision: nothing etcd did under the prefix from `sr` on was missed. -/
theorem cacheWatch_delivery (pfx key rangeEnd : GoString) (sr : w64) (L : List RespModel) :
    demuxPubBody (GF := GF) (etcdStepCert pfx) (some (keyPredForRange key rangeEnd)) sr none L ⊢
      ∃ (bs : List Batch) (p₀ : Int),
        ⌜eventsOf L = bs.flatten.filter (fun e => keyPredForRange key rangeEnd e.key) ∧
          SentOrdered L ∧ StreamOk bs ∧
          (sr ≠ W64 0 → p₀ < sint.Z sr ∧ ∀ b ∈ bs, sint.Z sr ≤ sint.Z (batchRev b))⌝ ∗
        certChain (etcdStepCert pfx) p₀ bs := by
  unfold demuxPubBody
  iintro ⟨%s, %v, %p₀, %Hf, #Hc, -⟩
  obtain ⟨hsr, hD, hp₀, -⟩ := Hf
  iexists streamRange s v.n v.stream, p₀
  iframe Hc
  ipureintro
  refine ⟨hD.events, hD.ordered, hD.stream_ok.sublist (List.filter_sublist ..), fun h => ?_⟩
  have hs : s = sr := by rcases hsr with h0 | h0; exact absurd h0 h; exact h0
  subst hs
  refine ⟨by rcases hp₀ with h0 | h0; exact absurd h0 h; exact h0, fun b hb => ?_⟩
  exact (streamRange_mem hb).2.1

/-- The same after a compaction at `n`: the log before the cancel response is complete up to `n`
(its batches are below `n`). -/
theorem cacheWatch_delivery_compacted (pfx key rangeEnd : GoString) (sr n : w64)
    (L : List RespModel) :
    demuxPubBody (GF := GF) (etcdStepCert pfx) (some (keyPredForRange key rangeEnd)) sr
        (some (some n)) L ⊢
      ∃ (bs : List Batch) (p₀ : Int),
        ⌜eventsOf L = bs.flatten.filter (fun e => keyPredForRange key rangeEnd e.key) ∧
          SentOrdered L ∧ StreamOk bs ∧ (∀ b ∈ bs, sint.Z (batchRev b) < sint.Z n) ∧
          (sr ≠ W64 0 → p₀ < sint.Z sr ∧ ∀ b ∈ bs, sint.Z sr ≤ sint.Z (batchRev b))⌝ ∗
        certChain (etcdStepCert pfx) p₀ bs := by
  unfold demuxPubBody
  iintro ⟨%s, %v, %p₀, %Hf, #Hc, -⟩
  obtain ⟨hsr, hD, hp₀, hn⟩ := Hf
  have hn' : n = v.n := hn n rfl
  subst hn'
  iexists streamRange s v.n v.stream, p₀
  iframe Hc
  ipureintro
  refine ⟨hD.events, hD.ordered, hD.stream_ok.sublist (List.filter_sublist ..),
    fun b hb => (streamRange_mem hb).2.2, fun h => ?_⟩
  have hs : s = sr := by rcases hsr with h0 | h0; exact absurd h0 h; exact h0
  subst hs
  refine ⟨by rcases hp₀ with h0 | h0; exact absurd h0 h; exact h0, fun b hb => ?_⟩
  exact (streamRange_mem hb).2.1

/-- The demux writer's state satisfies the demux's invariant. -/
theorem demuxWriter_inv (d : Loc) (γd : DemuxNames) (cap : Nat) (C : DemuxCert GF)
    (c : DemuxCore) :
    demuxWriter d γd cap C c ⊢ demuxWriter d γd cap C c ∗ ⌜DemuxInv cap c⌝ := by
  unfold demuxWriter
  iintro ⟨Hg, Hh, %Hi⟩
  iframe
  ipureintro; exact ⟨Hi, Hi⟩

end watchdefs

section cache
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- The `Cache` predicate (persistent): every field of the `Cache` but the wait group's state
points for good to `cf`'s values; `cf.ready` is a `ready` (ghost names `γr`), `cf.demux` a demux
(ghost names `γd`, history capacity `cap`), `cf.store` a store (ghost names `cf.γs`, history
capacity `cf.scap`), `cf.kv` a client of etcd for the prefix (`isEtcdKV`), `cf.watcher` its
watcher (`isEtcdWatcher`), the progress requestor a `*conditionalProgressRequestor`, the internal
context a context, `cf.clock` a clock, `cf.stop` the internal context's cancel function; the wait
group is a `WaitGroup` with the counter invariant `cacheWgInv`; and the configuration's
`PerWatcherBufferSize` is not negative (finding 5). -/
def isCacheFields (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames)
    (cap : Nat) : IProp GF :=
  iprop("#Hprefix" ∷ cachePrefixAddr c ↦□ cf.pfx ∗
    "#Hcfg" ∷ cacheCfgAddr c ↦□ cf.cfg ∗
    "#Hready" ∷ cacheReadyAddr c ↦□ cf.ready ∗
    "#Hdemux" ∷ cacheDemuxAddr c ↦□ cf.demux ∗
    "#HisReady" ∷ isReady cf.ready γr ∗
    "#HisDemux" ∷ isDemux cf.demux γd cap (etcdStepCert cf.pfx) ∗
    "#Hstore" ∷ cacheStoreAddr c ↦□ cf.store ∗
    "#HisStore" ∷ isStore cf.store cf.γs cf.scap ∗
    "#Hkv" ∷ cacheKvAddr c ↦□ GoInterface.ok cf.kv ∗
    "#HisKV" ∷ isEtcdKV cf.kv cf.pfx ∗
    "#Hpr" ∷ cachePrAddr c ↦□
      GoInterface.ok (interface.mk (go.GoType.PointerType conditionalProgressRequestor.ty) #cf.pr) ∗
    "#HisPR" ∷ isProgressRequestor cf.pr ∗
    "#Hwatcher" ∷ cacheWatcherAddr c ↦□ GoInterface.ok cf.watcher ∗
    "#HisWatcher" ∷ isEtcdWatcher cf.watcher cf.pfx ∗
    "#Hictx" ∷ cacheICtxAddr c ↦□ GoInterface.ok cf.ictx ∗
    "#HisICtx" ∷ (∃ ics : context.ContextDesc (IProp GF), context.isContext cf.ictx ics) ∗
    "#Hclock" ∷ cacheClockAddr c ↦□ GoInterface.ok cf.clock ∗
    "#HisClock" ∷ isClock cf.clock ∗
    "#HisWg" ∷ sync.isWaitGroup (cacheWgAddr c) cf.γwg cacheWgWGN ∗
    "#HwgInv" ∷ inv cacheWgN (cacheWgInv cf) ∗
    "#Hstop" ∷ cacheStopAddr c ↦□ cf.stop ∗
    "#HisStop" ∷ □ (∀ Φ : val → IProp GF, □ (True : IProp GF) -∗ ▷ (True -∗ Φ #()) -∗
      WP (App (Val #cf.stop) (Val #())) {{ Φ }}) ∗
    "%Hbuf" ∷ ⌜0 ≤ sint.Z cf.cfg.PerWatcherBufferSize'⌝)

instance isCacheFields_persistent (c : Loc) (cf : CacheFields) (γr : ReadyNames)
    (γd : DemuxNames) (cap : Nat) : Persistent (isCacheFields (GF := GF) c cf γr γd cap) := by
  unfold isCacheFields; infer_instance

/-- What `validateRange` returns: `nil` for a `validRange`, else the value of
`ErrKeyRangeInvalid`. -/
def rangeErr (pfx start end_ : GoString) (err : GoInterface) : IProp GF :=
  if validRange pfx start end_ then iprop(⌜err = GoInterface.nil⌝)
  else iprop(globalAddr ErrKeyRangeInvalid ↦□ err)

instance rangeErr_persistent (pfx start end_ : GoString) (err : GoInterface) :
    Persistent (rangeErr (GF := GF) pfx start end_ err) := by
  unfold rangeErr; split <;> infer_instance

/-- What `validateGet`/`validateWatch` return, for a request on `key` with range end
`rangeEnd` on a cache with prefix `pfx`: a non-nil error (`fmt.Errorf` wrapping
`ErrUnsupportedRequest`; the wrapping is not modelled) and no predicate if `unsupported`;
otherwise the value of `ErrKeyRangeInvalid` and no predicate if the range is not
`validRange`; otherwise `nil` and the `KeyPredForRange` closure. -/
def validateResult (unsupported : Bool) (pfx key rangeEnd : GoString) (f : GoFunc)
    (err : GoInterface) : IProp GF :=
  if unsupported then iprop(⌜f = func.nil⌝ ∗ ∃ e, ⌜err = GoInterface.ok e⌝ ∗ errorStringSpec e)
  else if validRange pfx key rangeEnd then
    iprop(⌜err = GoInterface.nil ∧ f ≠ func.nil⌝ ∗ keyPredSpec f (keyPredForRange key rangeEnd))
  else iprop(⌜f = func.nil⌝ ∗ globalAddr ErrKeyRangeInvalid ↦□ err)

instance validateResult_persistent (u : Bool) (pfx key rangeEnd : GoString) (f : GoFunc)
    (err : GoInterface) : Persistent (validateResult (GF := GF) u pfx key rangeEnd f err) := by
  unfold validateResult; split
  · infer_instance
  · split <;> infer_instance

/-! ## `Cache.Get` -/

/-- A reader's token of the cache's store, with the cache's certificates (`etcdCert`,
`etcdReached`). -/
def cacheReader (cf : CacheFields) : IProp GF :=
  storeReader cf.store cf.γs cf.scap (etcdCert cf.pfx) etcdReached

/-- What `waitTillRevision(ctx, rev)` returns: `nil` once the store's latest revision is at
least `rev`; the value of `ErrCacheTimeout`; or the context's (non-nil) error once it is
done. -/
def waitResult (cf : CacheFields) (s : context.ContextDesc (IProp GF)) (rev : w64)
    (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ storeRevLb cf.γs rev) ∨
    globalAddr ErrCacheTimeout ↦□ err ∨
    (⌜err ≠ GoInterface.nil⌝ ∗ □ s.PDone ∗ context.ContextClosed s.Done_gn))

/-- `Cache.Get`'s errors, for a request on `key` with `Op` `o` (`OpModel`), as the code returns
them: the context is done (waiting for the cache to be ready, or for the store to catch up);
an unsupported option (some non-nil error); a range outside the cache's prefix
(`ErrKeyRangeInvalid`); for a linearizable request (not `WithSerializable`), the client's error
(any), a revision above etcd's current one (`rpctypes.ErrFutureRev`), or the store not catching
up in time (`ErrCacheTimeout`); or the store's (`getSnapshot`'s) error for its state `st`. -/
def cacheGetErr (cf : CacheFields) (r0 : w64) (s : context.ContextDesc (IProp GF))
    (key : GoString) (o : OpModel) (err : GoInterface) : IProp GF :=
  iprop((⌜err ≠ GoInterface.nil⌝ ∗ □ s.PDone ∗ context.ContextClosed s.Done_gn) ∨
    ⌜o.getUnsupported = true ∧ err ≠ GoInterface.nil⌝ ∨
    (⌜o.getUnsupported = false ∧ validRange cf.pfx key o.rangeEnd = false⌝ ∗
      globalAddr ErrKeyRangeInvalid ↦□ err) ∨
    ⌜o.serializable = false ∧ err ≠ GoInterface.nil⌝ ∨
    (⌜o.serializable = false⌝ ∗ globalAddr v3rpc.rpctypes.ErrFutureRev ↦□ err ∗
      ∃ (serverRev : w64) (m : KvMap), isEtcdKvs serverRev cf.pfx m ∗
        ⌜sint.Z serverRev < sint.Z o.rev⌝) ∨
    (⌜o.serializable = false⌝ ∗ globalAddr ErrCacheTimeout ↦□ err) ∨
    (∃ st : StoreState, storeSeen cf.γs cf.scap r0 st ∗ snapErr (snapModel st o.rev) err ∗
      ⌜∀ r m, snapModel st o.rev ≠ .ok r m⌝))

/-- The `GetResponse` `Cache.Get` builds: `{Header: hdr, Kvs: kvs, Count: n}`. -/
def getRespVal (hdr : Loc) (kvs : GoSlice) (n : w64) : go_etcd_io.etcd.client.v3.GetResponse :=
  { (zero_val etcdserverpb.RangeResponse) with Header' := hdr, Kvs' := kvs, Count' := n }

/-- The `ResponseHeader` `Cache.Get` builds: `{Revision: rev}`. -/
def respHeaderVal (rev : w64) : etcdserverpb.ResponseHeader :=
  { (zero_val etcdserverpb.ResponseHeader) with Revision' := rev }

/-- `Cache.Get`'s answer, for a request on `key` with `Op` `o`: a fresh response (owned by the
caller) whose header revision is the store's latest revision in some state `st` (at least the
caller's `r0`), listing, in key order, the `*KeyValue`s of the snapshot `(r, m)` that
`getSnapshot(o.rev)` picks in `st` (`snapModel`: the greatest cached revision at most `o.rev`,
or at most `st.latestRev` for `o.rev = 0`) in the range `[key, o.rangeEnd)` (`kvRange`), with
its count; and `m` is etcd's state at `r` (`isEtcdKvs`). A linearizable request (not
`WithSerializable`) is moreover at least as fresh as etcd was when it started: etcd had a
state at a revision `serverRev`, at least the requested one, that the store's latest revision
has reached. -/
def cacheGetOk (cf : CacheFields) (r0 : w64) (key : GoString) (o : OpModel) (resp : Loc) :
    IProp GF :=
  iprop(∃ (hdr : Loc) (kvsSl : GoSlice) (st : StoreState) (r : w64) (m : KvMap),
    resp ↦ getRespVal hdr kvsSl (W64 (kvRange key o.rangeEnd m).length) ∗
    hdr ↦ respHeaderVal st.latestRev ∗
    kvsSl ↦* ((kvRange key o.rangeEnd m).map Prod.snd) ∗ ownSliceCap Loc kvsSl (DFrac.own 1) ∗
    kvsAt (kvRange key o.rangeEnd m) ∗
    isEtcdKvs r cf.pfx m ∗ storeSeen cf.γs cf.scap r0 st ∗
    ⌜snapModel st o.rev = .ok r m ∧ o.getUnsupported = false ∧
      validRange cf.pfx key o.rangeEnd = true⌝ ∗
    (if o.serializable then iprop(True)
     else iprop(∃ (serverRev : w64) (m' : KvMap), isEtcdKvs serverRev cf.pfx m' ∗
       ⌜sint.Z o.rev ≤ sint.Z serverRev ∧ sint.Z serverRev ≤ sint.Z st.latestRev⌝)))

/-- What `Cache.Get` returns: `nil` and an error (`cacheGetErr`), or a response
(`cacheGetOk`) and `nil`. -/
def cacheGetResult (cf : CacheFields) (r0 : w64) (s : context.ContextDesc (IProp GF))
    (key : GoString) (o : OpModel) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜resp = null⌝ ∗ cacheGetErr cf r0 s key o err) ∨
    (⌜err = GoInterface.nil⌝ ∗ cacheGetOk cf r0 key o resp))

end cache

theorem pairwise_le_getLast {V : Type} {f : V → Int} {l : List V}
    (h : l.Pairwise (fun a b => f a < f b)) {x y : V} (hx : x ∈ l) (hy : l.getLast? = some y) :
    f x ≤ f y := by
  obtain ⟨l', rfl⟩ := List.getLast?_eq_some_iff.1 hy
  rcases List.mem_append.1 hx with hx | hx
  · exact Int.le_of_lt ((List.pairwise_append.1 h).2.2 x hx y (List.mem_singleton_self _))
  · rw [List.mem_singleton.1 hx]; exact Int.le_refl _

/-- What `snapModel st rev = .ok r m` means: `(r, m)` is a snapshot of the history, at a revision
at most `rev` (at most the latest revision for `rev = 0`), the greatest such; and (with
`StoreInv`) at most the latest revision. The latest revision itself need not be `r` even for
`rev = 0`: a progress notification moves it without a snapshot. -/
theorem snapModel_ok_spec {cap : Nat} {st : StoreState} {rev r : w64} {m : KvMap}
    (hinv : StoreInv cap st) (h : snapModel st rev = .ok r m) :
    (r, m) ∈ st.history ∧ sint.Z r ≤ sint.Z st.latestRev ∧
    sint.Z r ≤ sint.Z (if rev = W64 0 then st.latestRev else rev) ∧
    ∀ h' ∈ st.history, sint.Z h'.1 ≤ sint.Z (if rev = W64 0 then st.latestRev else rev) →
      sint.Z h'.1 ≤ sint.Z r := by
  unfold snapModel at h
  by_cases h0 : st.latestRev = W64 0
  · rw [ite_eq_left h0] at h; cases h
  rw [ite_eq_right h0] at h
  by_cases hn : sint.Z rev < 0
  · rw [ite_eq_left hn] at h; cases h
  rw [ite_eq_right hn] at h
  generalize hrev' : (if rev = W64 0 then st.latestRev else rev) = rev' at h ⊢
  by_cases hf : sint.Z st.latestRev < sint.Z rev'
  · rw [ite_eq_left hf] at h; cases h
  rw [ite_eq_right hf] at h
  cases hlast : (st.history.filter (fun x => decide (sint.Z x.1 ≤ sint.Z rev'))).getLast? with
  | none => rw [hlast] at h; cases h
  | some x =>
    rw [hlast] at h
    cases h
    have hmem := List.mem_of_getLast? hlast
    rw [List.mem_filter] at hmem
    refine ⟨hmem.1, hinv.hist_le _ hmem.1, by simpa using hmem.2, ?_⟩
    intro h' hh' hle
    -- the last element of the filtered (sorted) history is its greatest
    have hin : h' ∈ st.history.filter (fun x => decide (sint.Z x.1 ≤ sint.Z rev')) :=
      List.mem_filter.2 ⟨hh', by simpa using hle⟩
    exact pairwise_le_getLast (f := fun x : w64 × KvMap => sint.Z x.1)
      (hinv.hist_sorted.filter _) hin hlast

end EtcdGrove
end Perennial
