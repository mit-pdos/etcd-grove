/-
Lean-first (no Rocq counterpart).

# The etcd3 watcher's consumer side: what the processing goroutines read (k8s 7f-5b)

`notes/k8s-7f5b-draft.md` §4-§5. The processing side (`serialProcessEvents`, or the concurrent
branch's scheduler, per-event goroutines and collector) calls `transform` on each raw event it takes
from `incomingEventChan` and `sendEvent` on each result. Here:

- `kRaw_transformOk` (pure): a raw event of the ideal raw stream at a state `σ` the caller's read
  update fired at meets `transform`'s premises (its values decode: `kvWfHist` for the state's records,
  `kvWritesDec` for an event's own value; its revision fits: `kvRevFits`);
- `kWcCons`: the watch channel's fields the consumers read, with `kWcProd` (persistent);
- `kProcSt`: the processing side's resources (the incoming channel's consumer half, `procd`'s half,
  `procEx`, the alive fraction);
- `wp_Empty_everything`: `storage.Everything`'s `Empty()` (`everythingOk`), and `selPredOkW` of it.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchProd
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.InvRunWg
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LogLemmas
public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__ShardingEnabled
public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__labelFieldEmpty

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE go_etcd_io.etcd.server.v3.etcdserver

/-! ## `transform`'s premises from the read laws (pure) -/

section pure
variable [GooseExts]

/-- The key-value a put leaves at its key holds the key and the value it wrote (a copy of the
compactor example's `findKey_putKv_kv`, `examples/k8s/compactor/KeyHist.lean`). -/
theorem kFindKey_putKv_kv {s : List EtcdKv} (r : w64) (k v : GoString) (l : w64) {kv : EtcdKv}
    (hs : s.Pairwise etcdKvLess) (h : mvcc.findKey k (putKv r k v l s) = some kv) :
    kv.key = k ∧ kv.value = v := by
  unfold putKv at h
  rw [mvcc.findKey_btInsert _ s hs] at h
  split at h
  · rename_i w hw
    have hk : w.key = k := by simpa using List.find?_some hw
    simp only [hk, ↓reduceIte, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  · simp only [↓reduceIte, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- **An event of a revision is one of its changes'** (the compactor example's `evsOfRevM_mem`,
strengthened): the change's key, and an event that is not a delete comes from a put, whose value it
holds. -/
theorem kEvsOfRevM_mem {r : Nat} {before : List EtcdKv} {cs : List mvcc.Change}
    (hs : before.Pairwise etcdKvLess) {ev : mvcc.EvM} (h : ev ∈ mvcc.evsOfRevM r before cs) :
    ∃ c ∈ cs, ev.kv.key = c.key ∧
      (ev.del = false → ∃ k v l, c = .put k v l ∧ ev.kv.value = v) := by
  unfold mvcc.evsOfRevM at h
  simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at h
  obtain ⟨i, -, kv, hkv, rfl⟩ := h
  have hev : (mvcc.evOfKv r kv).kv.key = kv.key ∧ (mvcc.evOfKv r kv).kv.value = kv.value := by
    unfold mvcc.evOfKv; split <;> simp
  rw [hev.1, hev.2]
  unfold mvcc.changeKv at hkv
  cases hc : cs[i]? with
  | none => rw [hc] at hkv; cases hkv
  | some c =>
    refine ⟨c, List.mem_of_getElem? hc, ?_⟩
    rw [hc] at hkv
    cases c with
    | put k v l =>
      simp only at hkv
      rw [List.take_add_one, hc, Option.toList_some] at hkv
      simp only [mvcc.applyChanges, List.foldl_append, List.foldl_cons, List.foldl_nil] at hkv
      have hsrt := mvcc.applyChanges_sorted (W64 r) (cs.take i) hs
      unfold mvcc.applyChanges at hsrt
      obtain ⟨hk, hv⟩ := kFindKey_putKv_kv (W64 r) k v l hsrt hkv
      exact ⟨hk, fun _ => ⟨k, v, l, rfl, hv⟩⟩
    | del k =>
      simp only [Option.some.injEq] at hkv
      subst hkv
      refine ⟨rfl, fun hd => ?_⟩
      exfalso
      revert hd
      unfold mvcc.evOfKv zeroKv
      simp

/-- An event of a range of revisions is in scope, an event of one of them, at its mod revision
(`kRangeEvsL_mem` with the revision's events). -/
theorem kRangeEvsL_mem_rev {σ : KVState} {inS : GoString → Bool} {lo hi : Nat} {ev : mvcc.EvM}
    (h : ev ∈ kRangeEvsL σ inS lo hi) :
    inS ev.kv.key = true ∧ ∃ r, lo ≤ r ∧ r < hi ∧ ev ∈ σ.revEvents r ∧
      ev.kv.modRev = W64 (r : Int) := by
  have hm := kRangeEvsL_mem h
  refine ⟨hm.1, ?_⟩
  unfold kRangeEvsL at h
  rw [List.mem_filter] at h
  obtain ⟨h, -⟩ := h
  simp only [List.mem_flatten, List.mem_map, List.mem_range'_1] at h
  obtain ⟨l, ⟨r, hr, rfl⟩, hev⟩ := h
  exact ⟨r, hr.1, by omega, hev, mvcc.evsOfRevM_modRev_sm r _ (KVStore.kvs_sorted _) _ ev hev⟩

theorem kSintZ_nonneg_of_nat {x : w64} {n : Nat} (hx : uint.nat x ≤ n) (hn : n + 3 < 2 ^ 63) :
    0 ≤ sint.Z x := by
  word

theorem kSintZ_W64 {r : Nat} (hn : r + 3 < 2 ^ 63) :
    0 ≤ sint.Z (W64 (r : Int)) ∧ sint.nat (W64 (r : Int)) = r := by
  constructor <;> word

end pure

section stores
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {Obj : Type} [DecidableEq Obj]

/-- A key in a watch's scope is under the store's prefix. -/
theorem kInScope_pfx (c : StoreCfg GF Obj) {kp : GoString} {recur : Bool} (hp : c.pfx <+: kp)
    {k : GoString} (h : kInScope kp recur k = true) : c.pfx <+: k := by
  unfold kInScope at h
  split at h
  · exact hp.trans (of_decide_eq_true h)
  · have := of_decide_eq_true h; subst this; exact hp

/-- **A raw event of the ideal raw stream meets `transform`'s premises** (`notes/k8s-7f5b-draft.md`
§5, `kInElemX_transformOk`): at a state `σ` whose revisions are the store's (`kvWfHist`), whose
writes decode (`kvWritesDec`) and whose revision fits (`kvRevFits`), with the scope under the
store's prefix, an initial key-value's value and an etcd event's values decode, and their revisions
are not negative. -/
theorem kRaw_transformOk (c : StoreCfg GF Obj) {σ : KVState} {kp : GoString} {recur : Bool}
    {inS : GoString → Bool} {m : KWatchMode} {st : Nat} {raws : List KRaw} {r : KRaw}
    (hwf : kvWfHist c σ) (hwd : kvWritesDec c σ) (hfit : kvRevFits σ.rev)
    (hpfx : c.pfx <+: kp) (hinS : inS = kInScope kp recur)
    (hsub : kRawStreamSub inS m σ st raws) (hr : r ∈ raws) :
    kRawDecOk c.S.dec σ r ∧ (∀ v, r = .kv v → 0 ≤ sint.Z v.modRev) ∧
      (∀ e, r = .ev e → 0 ≤ sint.Z e.kv.modRev) := by
  have hscope : ∀ k, inS k = true → c.pfx <+: k := by
    intro k hk; subst hinS; exact kInScope_pfx c hpfx hk
  unfold kvRevFits at hfit
  obtain ⟨hst, full, htail, hsl⟩ := hsub
  have hm : r ∈ kRawIdealL inS m σ st full := hsl.subset hr
  -- the tail's events
  have htl : ∀ {c0 : Nat} {l : List KRaw}, KRawTail σ inS c0 l → r ∈ l →
      kRawDecOk c.S.dec σ r ∧ (∀ v, r = .kv v → 0 ≤ sint.Z v.modRev) ∧
        (∀ e, r = .ev e → 0 ≤ sint.Z e.kv.modRev) := by
    intro c0 l ht hrl
    induction ht with
    | nil => cases hrl
    | bm c1 p rest _ _ _ _ ih =>
      rcases List.mem_cons.1 hrl with rfl | hrl
      · exact ⟨trivial, fun _ h => (by cases h), fun _ h => (by cases h)⟩
      · exact ih hrl
    | chg c1 r1 rest _ hr1 _ ih =>
      rcases List.mem_append.1 hrl with hrl | hrl
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hrl
        obtain ⟨hin, x, -, hx, hev, hmod⟩ := kRangeEvsL_mem_rev he
        have hxσ : x ≤ σ.rev := by omega
        have hW := kSintZ_W64 (r := x) (by omega)
        have hpk := hscope _ hin
        unfold KVState.revEvents at hev
        obtain ⟨ch, hch, hkey, hput⟩ := kEvsOfRevM_mem (KVStore.kvs_sorted _) hev
        refine ⟨⟨fun hd => ?_, fun _ pr hpr => ?_⟩, fun _ h => (by cases h), fun e' h => ?_⟩
        · obtain ⟨k, v, l, rfl, hv⟩ := hput hd
          rw [hv]
          simp only [mvcc.Change.key] at hkey
          exact hwd x hxσ _ hch k v l rfl (hkey ▸ hpk)
        · unfold kPrevAt at hpr
          rw [hmod, hW.2] at hpr
          have hf := findKey_kvs (σ.at (x - 1)) e.kv.key
          have hlk : (σ.at (x - 1)).lookup e.kv.key = some pr := hpr
          rw [hlk] at hf
          have hmem := List.mem_of_find?_eq_some hf
          have := (hwf (x - 1) (by omega) _ hmem).1 hpk
          exact this
        · cases h; rw [hmod]; exact hW.1
      · exact ih hrl
  unfold kRawIdealL at hm
  split at hm
  · rename_i hfi
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hm
      rw [List.mem_filter] at hv
      have hst' := hst hfi
      have hw := hwf st hst' v hv.1
      refine ⟨hw.1 (hscope _ hv.2), fun v' h => ?_, fun _ h => (by cases h)⟩
      cases h
      exact kSintZ_nonneg_of_nat (Nat.le_trans hw.2.2 hst') hfit
    · rcases List.mem_append.1 hm with hm | hm
      · split at hm
        · rcases List.mem_singleton.1 hm with rfl
          exact ⟨trivial, fun _ h => (by cases h), fun _ h => (by cases h)⟩
        · cases hm
      · exact htl htail hm
  · exact htl htail hm

/-- **The watch channel's fields the consumers read** (persistent; `notes/k8s-7f5b-draft.md` §4):
the producer's (`kWcProd`), the predicate `internalPred` (`selPredOkW`: the caller's, or
`storage.Everything` for an empty one), the result block logger, the store's watcher and the object
contract `transform` reads, and the scope under the store's prefix. -/
def kWcCons [Pos.Countable Obj] (wc sp : Loc) (c : StoreCfg GF Obj) (W : WatchSpec GF Obj) (γk : KVNames)
    (γ : KWatchNames) (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool)
    (inS : GoString → Bool) (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd alive : GName)
    (ctx : GoInterfaceOk) (kp : GoString) (recur : Bool) : IProp GF :=
  iprop(kWcProd wc sp c W γ cd sel emp inS m Q procd alive ctx kp recur ∗
    ∃ (p : k8s_io.apiserver.pkg.storage.SelectionPredicate) (lg : Loc),
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"internalPred" wc ↦□ p ∗
    selPredOkW c.S p sel emp ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"resultLogger" wc ↦□ lg ∗
    blockLoggerOk lg ∗ storeWatchOk sp c W γk ∗ transformerOk c.S c.ti ∗ versionerOk c.S c.vi ∗
    ⌜c.pfx <+: kp⌝)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance kWcCons_persistent [Pos.Countable Obj] (wc sp : Loc) (c : StoreCfg GF Obj) (W : WatchSpec GF Obj)
    (γk : KVNames) (γ : KWatchNames) (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool)
    (emp : Bool) (inS : GoString → Bool) (m : KWatchMode) (Q : Nat → KVState → IProp GF)
    (procd alive : GName) (ctx : GoInterfaceOk) (kp : GoString) (recur : Bool) :
    Persistent (kWcCons wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur) := by
  unfold kWcCons transformerOk versionerOk; infer_instance

/-- **The processing side's resources** (`notes/k8s-7f5b-draft.md` §4): the incoming channel's
consumer half (nothing received yet), `procd`'s half at `0`, `procEx` whole at `false`, and the
alive fraction `q`. -/
def kProcSt (γ : KWatchNames) (procd alive : GName) (q : Qp) : IProp GF :=
  iprop(spscConsumer γ.inc ([] : List Loc) ∗ dghostVar procd (DFrac.own (1 : Qp).half) 0 ∗
    dghostVar γ.procEx (DFrac.own 1) false ∗ kResAlive alive q)


/-- The namespace of `run`'s wait group (`resultChanWG`; `rwg`, three top-level slots). -/
abbrev rwgN : Namespace := nroot.@"k8sRunWg"

/-- **The processing goroutine's send commit** (`sendEvent`'s `S ∧ commit`): from a running
producer of `resultChan` (`kResAlive`) with its half of `procd` at `n`, the received element's facts
and its transform `e` held by `v`: `S` the two back (an aborted send), or the commit, after which
`procd`'s half is at `n + 1` (`kResInv_send_acc`). -/
theorem kRes_evCommit [Pos.Countable Obj] (c : StoreCfg GF Obj) (W : WatchSpec GF Obj) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd alive : GName) (chR : Loc) (q : Qp)
    (n : Nat) (r : KRaw) (raws' : List KRaw) (lbr lb0 st : Nat) (σr σ0 : KVState) (e : KWEv Obj)
    (v : k8s_io.apimachinery.pkg.watch.Event)
    (hlen : raws'.length = n) (hst : kStartOk m σ0 st)
    (hsub : kRawStreamSub inS m σr st (raws' ++ [r]))
    (he : kRawToEv c.S.dec sel emp c.S.zero σr r = some e) :
    ⊢ kResChan c W γ cd sel emp inS m Q procd alive chR -∗
      □ (∀ (l l' : Nat) (s s' : KVState), Q l s -∗ Q l' s' -∗ ⌜kvSameHist s s'⌝) -∗
      dghostVar procd (DFrac.own (1 : Qp).half) n -∗
      ([∗list] j ↦ x ∈ raws' ++ [r], monoListIdxOwn γ.raws j x) -∗
      □ Q lbr σr -∗ □ Q lb0 σ0 -∗
      (⌜kRawStreamOk inS m σr st (raws' ++ [r])⌝ ∨ kCancelled γ cd) -∗
      wevAt c.S W v e -∗ kResAlive alive q -∗
      ((kResAlive alive q ∗ dghostVar procd (DFrac.own (1 : Qp).half) n) ∧
        (£ 1 ∗ £ 1 ∗ £ 1 -∗ ∀ Φ : IProp GF,
          ▷ (kResAlive alive q ∗ dghostVar procd (DFrac.own (1 : Qp).half) (n + 1) -∗ Φ) -∗
          sendAu γ.res.chanName v Φ)) := by
  iintro #Hrc #Hh Hd Hbig #HQr #HQ0 Hok Hw HT
  isplit
  · iframe
  unfold kResChan
  icases Hrc with ⟨#Hch, #Hinv⟩
  iapply spsc_send_commit_inv γ.res chR (kResElem c W γ cd sel emp inS m Q) (fun _ => iprop(True))
    iprop(kResInv c γ cd sel emp inS m Q procd ∨ kResClosed alive) (kResAlive alive q)
    (dghostVar procd (DFrac.own (1 : Qp).half) (n + 1)) v
    $$ Hch Hinv [] HT
  · iapply kResChan_nc
  iintro HT HX
  iapply kResInv_send_acc c W γ cd sel emp inS m Q procd alive q n r raws' lbr lb0 st σr σ0 e v
    hlen hst hsub he $$ Hh Hd Hbig HQr HQ0 Hok Hw HT HX

/-- **The processing goroutine's filtered raw event** (`transform` gave `nil`): `kResInv_filter`
inside `kResChan`'s invariant, with a later credit. -/
theorem kRes_filterStep [Pos.Countable Obj] (c : StoreCfg GF Obj) (W : WatchSpec GF Obj)
    (γ : KWatchNames) (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool)
    (inS : GoString → Bool) (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd alive : GName)
    (chR : Loc) (q : Qp) (n : Nat) (r : KRaw) (raws' : List KRaw) (lbr lb0 st : Nat)
    (σr σ0 : KVState) (hlen : raws'.length = n) (hst : kStartOk m σ0 st)
    (hsub : kRawStreamSub inS m σr st (raws' ++ [r]))
    (hnone : kRawToEv c.S.dec sel emp c.S.zero σr r = none) :
    ⊢ kResChan c W γ cd sel emp inS m Q procd alive chR -∗
      □ (∀ (l l' : Nat) (s s' : KVState), Q l s -∗ Q l' s' -∗ ⌜kvSameHist s s'⌝) -∗
      dghostVar procd (DFrac.own (1 : Qp).half) n -∗
      ([∗list] j ↦ x ∈ raws' ++ [r], monoListIdxOwn γ.raws j x) -∗
      □ Q lbr σr -∗ □ Q lb0 σ0 -∗
      (⌜kRawStreamOk inS m σr st (raws' ++ [r])⌝ ∨ kCancelled γ cd) -∗
      kResAlive alive q -∗ £ 1 -∗
      |={⊤}=> kResAlive alive q ∗ dghostVar procd (DFrac.own (1 : Qp).half) (n + 1) := by
  iintro #Hrc #Hh Hd Hbig #HQr #HQ0 Hok HT Hlc
  unfold kResChan
  icases Hrc with ⟨#Hch, #Hinv⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  icases Hi with ⟨Hsp, HX⟩
  imod kResInv_filter c γ cd sel emp inS m Q procd alive q n r raws' lbr lb0 st σr σ0 hlen hst
    hsub hnone $$ Hh Hd Hbig HQr HQ0 Hok HT HX with ⟨HX, HT, Hd⟩
  imod Hclose $$ [Hsp HX] with -
  · inext; iframe
  imodintro
  iframe

set_option maxHeartbeats 800000 in
/-- **`run`'s close of `resultChan`** (after `resultChanWG.Wait()`, holding the whole alive token): the
producer token out of `kResInv` into the closed SPSC (`R := True`), `kResClosed` left in the invariant (a
copy of Perennial's `spsc_close_au` over `kResChan`'s one invariant). -/
theorem kRes_close_au [Pos.Countable Obj] (c : StoreCfg GF Obj) (W : WatchSpec GF Obj) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd alive : GName) (chR : Loc)
    (Φ : IProp GF) :
    ⊢ kResChan c W γ cd sel emp inS m Q procd alive chR -∗ £ 1 -∗ kResAlive alive 1 -∗ ▷ Φ -∗
      closeAu γ.res.chanName k8s_io.apimachinery.pkg.watch.Event Φ := by
  unfold kResChan closeAu
  iintro ⟨#Hchan, #Hinv⟩ Hlc1 HT Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  icases Hi with ⟨Hi, HX⟩
  icases HX with (HI | HC)
  · unfold kResInv
    icases HI with ⟨%sent, %evs, %raws, %σ, Hprod, -⟩
    unfold kResAlive
    imod dghostVar_update true alive false $$ HT with HC
    icases spscInv_elim _ _ _ $$ Hi with ⟨%s, %sent0, %recv, Hch, HsentI, HrecvI, %Hrel, Hm⟩
    unfold spscProducer
    ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hprod HsentI
    subst Heq
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    cases s with
    | Buffered buff =>
      dsimp only
      iintro Hoc
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI Hm Hprod HC] with -
      · inext
        isplitr [HC]
        · iapply spscInv_intro γ.res _ _ (.Closed buff) sent recv (by simpa [inflight] using Hrel)
            $$ Hoc HsentI HrecvI
          cases buff with
          | nil =>
            simp only [spscInvMatch, spscProducer]
            isplitl [Hprod]
            · iexact Hprod
            · ileft; itrivial
          | cons w ws =>
            simp only [spscInvMatch, spscProducer]
            isplitl [Hm]
            · iexact Hm
            isplitl [Hprod]
            · iexact Hprod
            · ileft; itrivial
        · iright; unfold kResClosed; iexact HC
      imodintro
      iexact Hcont
    | Idle =>
      dsimp only
      iintro Hoc
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI Hprod HC] with -
      · inext
        isplitr [HC]
        · iapply spscInv_intro γ.res _ _ (.Closed []) sent recv (by simpa [inflight] using Hrel)
            $$ Hoc HsentI HrecvI
          simp only [spscInvMatch, spscProducer]
          isplitl [Hprod]
          · iexact Hprod
          · ileft; itrivial
        · iright; unfold kResClosed; iexact HC
      imodintro
      iexact Hcont
    | Closed d =>
      dsimp only
      cases d with
      | nil =>
        simp only [spscInvMatch, spscProducer]
        icases Hm with ⟨Hp2, -⟩
        iapply dghostVar_three_halves $$ Hprod HsentI Hp2
      | cons _ _ =>
        simp only [spscInvMatch, spscProducer]
        icases Hm with ⟨-, Hp2, -⟩
        iapply dghostVar_three_halves $$ Hprod HsentI Hp2
    | _ => itrivial
  · iexfalso
    iapply kResAlive_closed $$ [$HT $HC]

/-- **The watch's ghost state** (`createWatchChan`, after `WithCancel`; `notes/k8s-7f5b-draft.md` §5):
over the names `γ0` gives (`kCancelPD`'s `stop`, `prodEx`, `procEx`, made before `WithCancel`, and `wc.ctx`'s
`wcDone`), and the two channels made empty, the SPSCs of `incomingEventChan` and of `resultChan` (its
one invariant with the producers' `kResInv`), the raw and sent events' lists, `procd` and `alive`: the
producer's state (`kProdSt`), the processing side's (`kProcSt`, the whole `alive`), and the
consumer's half of `resultChan`. -/
theorem kWatch_alloc [Pos.Countable Obj] (c : StoreCfg GF Obj) (W : WatchSpec GF Obj) (γ0 : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (chI chR : Loc) (γcI γcR : ChanNames) :
    ⊢ isChan chI γcI Loc -∗ ownChan γcI Loc (.Buffered []) -∗
      isChan chR γcR k8s_io.apimachinery.pkg.watch.Event -∗
      ownChan γcR k8s_io.apimachinery.pkg.watch.Event (.Buffered []) -∗
      dghostVar γ0.procEx (DFrac.own 1) false ={⊤}=∗
      ∃ (inc res : SpscNames) (raws evs procd alive : GName),
        isSpsc inc chI (kInElem { γ0 with inc := inc, res := res, raws := raws, evs := evs } cd inS m Q)
          (fun _ => iprop(False)) ∗
        kResChan c W { γ0 with inc := inc, res := res, raws := raws, evs := evs } cd sel emp inS m Q
          procd alive chR ∗
        kProdSt { γ0 with inc := inc, res := res, raws := raws, evs := evs } cd [] ∗
        kProcSt { γ0 with inc := inc, res := res, raws := raws, evs := evs } procd alive 1 ∗
        spscConsumer res ([] : List k8s_io.apimachinery.pkg.watch.Event) := by
  iintro #HcI HoI #HcR HoR Hpx
  imod mono_list_own_alloc (GF := GF) ([] : List KRaw) with ⟨%raws, Hr, #Hrlb⟩
  ihave ⟨Hr1, Hr2⟩ : monoListAuthOwn (GF := GF) raws (1 : Qp).half ([] : List KRaw) ∗
      monoListAuthOwn (GF := GF) raws (1 : Qp).half ([] : List KRaw) $$ [Hr]
  · iapply ((monoListAuthOwn_fractional (GF := GF) raws ([] : List KRaw)).fractional
      (1 : Qp).half (1 : Qp).half).1
    rw [Qp.half_add_half]; iexact Hr
  imod mono_list_own_alloc (GF := GF) ([] : List (KWEv Obj)) with ⟨%evs, He, -⟩
  imod dghostVar_alloc (GF := GF) (0 : Nat) with ⟨%procd, Hpd⟩
  icases dghostVar_halves _ _ $$ Hpd with ⟨Hpd1, Hpd2⟩
  imod dghostVar_alloc (GF := GF) false with ⟨%alive, Hal⟩
  imod start_spsc chI (kInElem { γ0 with raws := raws } cd inS m Q) (fun _ => iprop(False)) γcI
    $$ HcI [HoI] with ⟨%inc, #Hinc, Hip, Hic⟩
  · iright; iexact HoI
  imod dghostVar_alloc (GF := GF) ([] : List k8s_io.apimachinery.pkg.watch.Event) with ⟨%γsent, Hsent⟩
  icases dghostVar_halves _ _ $$ Hsent with ⟨HsentA, HsentF⟩
  imod dghostVar_alloc (GF := GF) ([] : List k8s_io.apimachinery.pkg.watch.Event) with ⟨%γrecv, Hrecv⟩
  icases dghostVar_halves _ _ $$ Hrecv with ⟨HrecvA, HrecvF⟩
  let res : SpscNames := ⟨γcR, γsent, γrecv⟩
  let γ : KWatchNames := { γ0 with inc := inc, res := res, raws := raws, evs := evs }
  imod inv_alloc nroot ⊤ iprop(spscInv res (kResElem c W γ cd sel emp inS m Q) (fun _ => iprop(True)) ∗
      (kResInv c γ cd sel emp inS m Q procd ∨ kResClosed alive))
    $$ [HoR HsentA HrecvA HsentF He Hpd1] with #Hinv
  · inext
    isplitl [HoR HsentA HrecvA]
    · iapply spscInv_intro res _ _ (.Buffered []) [] [] (by simp [inflight]) $$ HoR HsentA HrecvA
      simp only [spscInvMatch]
      iapply BigSepL.bigSepL_nil.2
      iempintro
    · ileft
      unfold kResInv
      iexists [], [], [], default
      unfold spscProducer
      iframe
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact Hrlb
      isplitr
      · ipureintro; rfl
      ileft; ipureintro; rfl
  imodintro
  iexists inc, res, raws, evs, procd, alive
  have hP : kInElem (GF := GF) { γ0 with inc := inc, res := res, raws := raws, evs := evs } cd inS m Q =
      kInElem { γ0 with raws := raws } cd inS m Q := by
    unfold kInElem kCancelled kStopped kProcExited; rfl
  rw [hP]
  isplitr
  · iexact Hinc
  isplitr
  · unfold kResChan
    iframe #
  isplitl [Hip Hr1 Hr2]
  · unfold kProdSt kIncTok
    isplitl [Hip Hr1]
    · iexists [], []
      iframe
      ipureintro; rfl
    · iexists []
      iframe
      isplitr
      · ipureintro; exact List.Sublist.refl _
      · ileft; ipureintro; rfl
  isplitl [Hic Hpd2 Hal Hpx]
  · unfold kProcSt kResAlive
    iframe
  unfold spscConsumer
  iexact HrecvF

/-- **Every context's `Err()` returns client errors**, from the client's watcher (its connection's
facts, `ctxErrClientAllW`): `createWatchChan`'s `wc.ctx`. -/
theorem clientWatchOk_ctxErr (cl : Loc) (γk : KVNames) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) :
    clientWatchOk (GF := GF) cl γk ∗ context.isContext ctx cs ⊢ ctxErrClient ctx cs := by
  iintro ⟨#Hcw, #Hctx⟩
  iunfold clientWatchOk at Hcw
  icases Hcw with ⟨%w, %V, -, #Hw, -⟩
  iunfold client.isClientWatcher at Hw
  icases Hw with ⟨%cs', %vs, -, -, -, -, -, -, -, Hsf, -⟩
  iunfold client.watchSrvFacts at Hsf
  icases Hsf with ⟨-, Hcf⟩
  iunfold client.watchConnFacts at Hcf
  icases Hcf with ⟨-, -, -, -, -, -, #Hca, -, -⟩
  iunfold client.ctxErrClientAllW at Hca
  iapply Hca $$ Hctx

end stores

/-! ## `storage.Everything` (`createWatchChan`'s predicate for an empty one; k8s 7f-5b H2 (c)) -/

section everything
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

/-- A selector whose `Empty()` returns `true` (`everythingOk`'s triples) meets `selEmptyOk`. -/
theorem selEmptyOk_of_triple (i : GoInterfaceOk) :
    ({{ True }} (App (Val #(methods i.ty go!"Empty" i.v)) (Val #())) {{ RET #true; True }} :
      IProp GF) ⊢ selEmptyOk (GoInterface.ok i) true := by
  iintro #H
  unfold selEmptyOk
  iexists i
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %Φ HΦ
  iapply H
  · itrivial
  inext
  iintro -
  iexact HΦ

/-- **`Empty()` of `storage.Everything`** (`everythingOk`): `ShardingEnabled()` is `false` on the
`nil` shard selector, and `labelFieldEmpty()` calls the two selectors' `Empty()`, both `true`. -/
theorem wp_Empty_everything
    (wp_ShardingEnabled : storage.SelectionPredicate.ShardingEnabled.spec (GF := GF) (hG := hG))
    (wp_labelFieldEmpty : storage.SelectionPredicate.labelFieldEmpty.spec (GF := GF) (hG := hG))
    (pp : Loc) (dq : DFrac) (p : k8s_io.apiserver.pkg.storage.SelectionPredicate) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗ pp ↦{dq} p ∗
        _root_.Perennial.k8s_io.apiserver.pkg.storage.etcd3.everythingOk p }}
      (App (Val (pp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.SelectionPredicate.ty
        @!! go!"Empty")) (Val #()))
    {{ RET #true; pp ↦{dq} p }} := by
  wp_start as ⟨Hp, #He⟩
  unfold _root_.Perennial.k8s_io.apiserver.pkg.storage.etcd3.everythingOk
  icases He with ⟨%hs, ⟨%il, %hil, #HlE⟩, ⟨%ifd, %hif, #HfE⟩⟩
  ihave #Hle : selEmptyOk (GF := GF) p.Label' true $$ []
  · rw [hil]; iapply selEmptyOk_of_triple $$ HlE
  ihave #Hfe : selEmptyOk (GF := GF) p.Field' true $$ []
  · rw [hif]; iapply selEmptyOk_of_triple $$ HfE
  (try wp_auto)
  wp_apply (wp_ShardingEnabled pp dq p hs) $$ [$Hp] as Hp
  (try wp_auto)
  wp_apply (wp_labelFieldEmpty pp dq p true true) $$ [$Hp $Hle $Hfe] as Hp
  (try wp_auto)
  iapply HΦ $$ Hp

/-- **`storage.Everything` as the watcher reads it** (`selPredOkW`, empty, selecting everything). -/
theorem everything_selPredOkW
    (wp_ShardingEnabled : storage.SelectionPredicate.ShardingEnabled.spec (GF := GF) (hG := hG))
    (wp_labelFieldEmpty : storage.SelectionPredicate.labelFieldEmpty.spec (GF := GF) (hG := hG))
    {Obj : Type} (S : ObjSpec GF Obj) (p : k8s_io.apiserver.pkg.storage.SelectionPredicate)
    (sel : Obj → Bool) (hsel : ∀ o, sel o = true) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗
      _root_.Perennial.k8s_io.apiserver.pkg.storage.etcd3.everythingOk p ⊢
      selPredOkW S p sel true := by
  iintro ⟨#Hpkg, #He⟩
  ihave #He' := He
  unfold _root_.Perennial.k8s_io.apiserver.pkg.storage.etcd3.everythingOk
  icases He' with ⟨%hs, -, -⟩
  unfold selPredOkW
  isplitr
  · ipureintro; exact ⟨hs, fun _ => hsel⟩
  isplitr
  · imodintro; iintro %h; cases h
  imodintro
  iintro %pp %dq %Φ Hp HΦ
  iapply (wp_Empty_everything wp_ShardingEnabled wp_labelFieldEmpty pp dq p) $$ [$Hp]
  · iframe #
    unfold _root_.Perennial.k8s_io.apiserver.pkg.storage.etcd3.everythingOk
    iexact He
  inext
  iexact HΦ

end everything

end k8s
end EtcdGrove
end Perennial
