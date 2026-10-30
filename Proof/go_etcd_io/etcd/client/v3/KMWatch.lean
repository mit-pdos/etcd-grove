/-
**A client watcher of etcd's KV meets the cache's watcher contracts** (D48, 2026-10-26).
Lean-first, no Rocq counterpart.

`isEtcdWatcher_of_km`: a `*watcher` of etcd's KV `γ.kv` (`isKvWatcher`), with the adapter's
invariant (`kmInv γ`, `EtcdModelKV.lean`), meets the cache's watch contract (`isEtcdWatcher`,
`cache/v3/InvEtcd.lean`) at the adapter's model (`etcdModelOfKV γ`), for a non-empty prefix not
all `0xff`: the call is `watcher.Watch.spec`'s, with the adapter's read update after the floor
the caller knows (`km_read_au` at `km_reached_lb`'s changes of `etcdRead (rev - 1)`), and each
response, a read of a state the client saw (`watchStateRespOk`), is etcd's response of the
cache's contract (`watchRespOk_of_km`):
* a progress notification past the cursor is a step without events (`kmStep`) of the log of the
  state it read, through its revision (`kvLogOkTo`); at the watch's start, the caller's floor;
* events are the range's events of that log (`rangeEvents_take`: mvcc's watch events of the
  prefix's range `pfxRange`), so a chain of steps (`km_chain`), one per revision.
`isEtcdProgressNotifier_of_km`: `RequestProgress` from `isKvWatcher` (`ServerWatcher.lean`'s).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.EtcdModelKV
public import Proof.go_etcd_io.etcd.client.v3.WatchStateDefs
public import Proof.go_etcd_io.etcd.client.v3.PrefixRange
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchStep
public import Proof.go_etcd_io.etcd.client.v3.ServerWatcher
public import Proof.go_etcd_io.etcd.client.v3.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3
  go_etcd_io.etcd.server.v3.etcdserver mvcc txn

section pure
variable [GooseExts]

/-! ## Batches and watch events (pure; `WatchCompl.lean`'s and `WatchContent.lean`'s, copied so
that this bridge does not rest on the watch pipeline's files) -/

theorem km_splitBatches_head : ∀ B : List EvModel,
    (splitBatches B).head?.map batchRev = B.head?.map EvModel.rev
  | [] => rfl
  | e :: es => by
    unfold splitBatches
    split
    · rfl
    · split <;> rfl

/-- A leading block of one revision `x`'s events, followed by events not starting at `x`, is the
first batch. -/
theorem km_splitBatches_block (x : w64) (B : List EvModel)
    (hB : ∀ e, B.head? = some e → e.rev ≠ x) :
    ∀ A : List EvModel, A ≠ [] → (∀ e ∈ A, e.rev = x) →
      splitBatches (A ++ B) = A :: splitBatches B
  | [], h, _ => absurd rfl h
  | [e], _, hA => by
    have he : e.rev = x := hA e List.mem_cons_self
    show splitBatches (e :: B) = [e] :: splitBatches B
    rw [splitBatches.eq_2]
    cases hs : splitBatches B with
    | nil =>
      have : B = [] := by
        cases B with
        | nil => rfl
        | cons b bs =>
          have h1 := km_splitBatches_head (b :: bs)
          rw [hs] at h1; simp at h1
      subst this; rfl
    | cons b bs =>
      have h1 := km_splitBatches_head B
      rw [hs] at h1
      cases B with
      | nil => simp at h1
      | cons b0 bs0 =>
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at h1
        have hne := hB b0 rfl
        simp only
        have hc : ¬ batchRev b = e.rev := by rw [h1, he]; exact hne
        simp only [hc, ↓reduceIte]
  | e :: e' :: A', _, hA => by
    have ih := km_splitBatches_block x B hB (e' :: A') (by simp)
      (fun y hy => hA y (List.mem_cons_of_mem _ hy))
    show splitBatches (e :: (e' :: A' ++ B)) = (e :: e' :: A') :: splitBatches B
    rw [splitBatches.eq_2, show e' :: A' ++ B = e' :: (A' ++ B) from rfl] at *
    rw [ih]
    have h1 : batchRev (e' :: A') = e.rev := by
      show e'.rev = e.rev
      rw [hA e' (List.mem_cons_of_mem _ List.mem_cons_self), hA e List.mem_cons_self]
    simp only [h1, ↓reduceIte]

theorem km_pairwise_of_const {α : Type} (g : α → Int) (c : Int) :
    ∀ l : List α, (∀ x ∈ l, g x = c) → l.Pairwise (fun a b => g a ≤ g b)
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    refine List.Pairwise.cons (fun y hy => ?_)
      (km_pairwise_of_const g c xs (fun y hy => h y (by simp [hy])))
    rw [h x (by simp), h y (by simp [hy])]; exact Int.le_refl _

/-- A range's watch events are in revision order (of a log shorter than `2 ^ 63`). -/
theorem km_watchEvents_sorted (L : Log) (hlen : L.length < 2 ^ 63) (r : WatchRange) (a b : Nat) :
    (watchEvents L r a b).Pairwise (fun e f => sint.Z e.kv.modRev ≤ sint.Z f.kv.modRev) := by
  unfold watchEvents
  refine List.Pairwise.filter _ ?_
  unfold logEvents
  rw [List.pairwise_flatten, List.pairwise_map]
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨m, -, rfl⟩ := List.mem_map.1 hl
    exact km_pairwise_of_const (fun e : EvM => sint.Z e.kv.modRev) (sint.Z (W64 (m : Int))) _
      (fun x hx => by rw [evsOfRevM_modRev_sm m _ (stateAt_sorted _ _) _ x hx])
  · refine List.Pairwise.imp_of_mem ?_ (List.pairwise_lt_range' (s := a) (n := b - a))
    intro m1 m2 _ _ hlt x hx y hy
    have hy2 : m2 < L.length := by
      refine Classical.byContradiction fun hc => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hy
      simp [evsOfRevM_nil] at hy
    rw [evsOfRevM_modRev_sm m1 _ (stateAt_sorted _ _) _ x hx,
      evsOfRevM_modRev_sm m2 _ (stateAt_sorted _ _) _ y hy]
    have h1 : sint.Z (W64 (m1 : Int)) = m1 := by word
    have h2 : sint.Z (W64 (m2 : Int)) = m2 := by word
    omega

/-- A registered range covering exactly the watch's range: its watch events are the watch's
range events of the log. -/
theorem km_rangeLogEvents_watchEvents (L : Log) (o : OpFull) (rg : WatchRange)
    (hcov : ∀ k, rg.covers k = inRange o.key o.base.rangeEnd k) (lo hi : Nat) :
    rangeLogEvents L o lo hi = watchEvents L rg lo hi := by
  unfold rangeLogEvents watchEvents
  congr 1
  funext ev
  rw [hcov]

/-! ## The prefix's range (pure) -/

/-- The registered range of a prefix watch on `pfx` (its key and range end). -/
def pfxRange (pfx : GoString) : WatchRange := ⟨pfx, some (prefixRangeEnd pfx), W64 0, W64 0⟩

theorem pfxRange_covers (pfx : GoString) (hp : pfx ≠ []) (hff : prefixRangeEnd pfx ≠ [W8 0])
    (k : GoString) : (pfxRange pfx).covers k = inRange pfx (prefixRangeEnd pfx) k := by
  have h0 : prefixRangeEnd pfx ≠ [] := concurrency.prefixRangeEnd_ne_nil _
  unfold WatchRange.covers inRange pfxRange
  simp only [if_neg h0, if_neg hff]
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, adt.affCmp_nonneg_iff, adt.affCmp_neg_iff, adt.affLt]
  by_cases hk0 : k = go!""
  · subst hk0
    have hlt : go.GoStringLt [] pfx := by
      obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil hp
      rw [ht]; exact go.goStringLt_nil_cons a t
    simp [hlt]
  · simp [hk0, hp, h0]

theorem pfxRange_cov (pfx : GoString) (hp : pfx ≠ []) (hff : prefixRangeEnd pfx ≠ [W8 0]) :
    ∀ k, (pfxRange pfx).covers k = true ↔ pfx <+: k := by
  intro k
  rw [pfxRange_covers pfx hp hff k]
  exact concurrency.inRange_prefix pfx k hp

/-! ## The state's events, as a log's (pure) -/

theorem kvLogOkTo_len {σ : KVState} {r : Nat} (h : kvLogOkTo σ r) :
    σ.log.length = σ.rev + 1 ∧ σ.rev = σ.changes.length := by
  have hc : σ.compacted = 0 := by rw [h.1]; rfl
  constructor
  · simp only [KVState.log, List.length_cons, KVState.rev, hc]; omega
  · simp only [KVState.rev, hc]; omega

/-- **A prefix watch's events of a well-formed state**, through a revision `r` it is well formed
to: mvcc's watch events of the prefix's range on its log up to `r`. -/
theorem rangeEvents_take (σ : KVState) (o : OpFull) (pfx : GoString) (hp : pfx ≠ [])
    (hff : prefixRangeEnd pfx ≠ [W8 0]) (hk : o.key = pfx)
    (he : o.base.rangeEnd = prefixRangeEnd pfx) (r : Nat) (h : kvLogOkTo σ r) (lo hi : Nat)
    (h0 : 0 < lo) (hh : hi ≤ r + 1) :
    σ.rangeEvents o lo hi = watchEvents (σ.log.take (r + 1)) (pfxRange pfx) lo hi := by
  obtain ⟨hl, -⟩ := kvLogOkTo_len h
  have hr := h.2.1
  have h1 := rangeEvents_kvStateOf σ.log o lo hi h0 (by omega)
  rw [← h.1] at h1
  rw [h1, ← rangeLogEvents_prefix (List.take_prefix (r + 1) σ.log) o
    (by rw [List.length_take]; omega)]
  exact km_rangeLogEvents_watchEvents _ o _
    (fun k => by rw [hk, he]; exact pfxRange_covers pfx hp hff k) lo hi

/-- A list of events' revisions are their state events' (pointwise). -/
theorem map_rev_eq (es : List EvModel) (evs : List EvM) (hl : es.length = evs.length)
    (hpt : ∀ (i : Nat) (e : EvModel) (ev : EvM), es[i]? = some e → evs[i]? = some ev →
      e.rev = ev.kv.modRev) :
    es.map EvModel.rev = evs.map (fun ev => ev.kv.modRev) := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp only [List.getElem_map]
  simp only [List.length_map] at h1 h2
  exact hpt i _ _ (List.getElem?_eq_getElem h1) (List.getElem?_eq_getElem h2)

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-! ## Logs the client saw -/

/-- **The log of a state the client saw, through a revision it is well formed to**. -/
theorem kmLog_take (γ : KMNames) (σ : KVState) (r : Nat) (h : kvLogOkTo σ r) :
    monoListLbOwn (GF := GF) γ.ch σ.changes ⊢ kmLog γ (σ.log.take (r + 1)) := by
  obtain ⟨hl, -⟩ := kvLogOkTo_len h
  obtain ⟨-, hr, hr63, hw, hs⟩ := h
  iintro #Hlb
  unfold kmLog
  iexists σ.changes
  iframe Hlb
  ipureintro
  refine ⟨List.take_prefix _ _, hw, ?_, hs⟩
  rw [List.length_take]; omega

/-- etcd has reached every revision of a log the client saw. -/
theorem kmLog_reached (γ : KMNames) (L : Log) (n : Nat) (hn : n < L.length) (h63 : n < 2 ^ 63) :
    kmLog (GF := GF) γ L ⊢ etcdReached (EM := etcdModelOfKV γ) (W64 (n : Int)) := by
  unfold kmLog
  iintro ⟨%l, #Hl, %h⟩
  have := h.1.length_le
  simp only [List.length_cons] at this
  ihave ⟨#H, -⟩ := km_reached_of γ l n (by omega) h63 $$ Hl
  iexact H

/-- **A step of a log the client saw, from its watch events**: no watch event of the prefix's
range in `[p + 1, b)`, the events of `b`. -/
theorem km_step_of (γ : KMNames) (L : Log) (hwf : LogWf' L) (hlen : L.length < 2 ^ 63)
    (pfx : GoString) (rg : WatchRange) (hcov : ∀ k, rg.covers k = true ↔ pfx <+: k) (p b : Nat)
    (hpb : p ≤ b) (hb : b < L.length) (hnone : watchEvents L rg (p + 1) b = []) :
    kmLog (GF := GF) γ L ⊢ kmStep γ (W64 (p : Int)) (W64 (b : Int)) pfx
      ((watchEvents L rg b (b + 1)).map v3rpc.evmToEtcd) := by
  have hnone' : ∀ x : Nat, p < x → x < b → watchEvents L rg x (x + 1) = [] := by
    intro x h1 h2
    have := hnone
    rw [watchEvents_append L rg (show p + 1 ≤ x by omega) (show x ≤ b by omega),
      watchEvents_append L rg (show x ≤ x + 1 by omega) (show x + 1 ≤ b by omega)] at this
    exact (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 this).2).1
  obtain ⟨hz, hs⟩ := v3rpc.watchStreamSpec_step L hwf hlen rg pfx hcov p b hnone'
  have e0 : sint.Z (W64 (p : Int)) = p := by word
  have e1 : sint.Z (W64 (b : Int)) = b := by word
  iintro #HL
  unfold kmStep
  iexists L
  iframe HL
  ipureintro
  refine ⟨by omega, by omega, by omega, fun x hx1 hx2 => hz x (by omega) (by omega), ?_⟩
  rw [e1]; simpa using hs

/-! ## Delivered events -/

theorem eventsIs_pure (es : List EvModel) (evs : List EvM) :
    eventsIs (GF := GF) es evs ⊢ ⌜es.length = evs.length ∧ ∀ (i : Nat) (e : EvModel) (ev : EvM),
      es[i]? = some e → evs[i]? = some ev →
      e.typ = (if ev.del then W32 1 else W32 0) ∧ e.key = ev.kv.key ∧ e.rev = ev.kv.modRev⌝ := by
  unfold eventsIs
  iintro ⟨%hl, #H⟩
  ihave %Hall : ⌜∀ (i : Nat) (e : EvModel) (ev : EvM), es[i]? = some e → evs[i]? = some ev →
      e.typ = (if ev.del then W32 1 else W32 0) ∧ e.key = ev.kv.key ∧ e.rev = ev.kv.modRev⌝ $$ [H]
  · iapply (pure_forall (PROP := IProp GF)).2
    iintro %i
    iapply (pure_forall (PROP := IProp GF)).2
    iintro %e
    iapply (pure_forall (PROP := IProp GF)).2
    iintro %ev
    iapply (pure_wand (PROP := IProp GF)).1
    iintro %h1
    iapply (pure_wand (PROP := IProp GF)).1
    iintro %h2
    ihave Hx := H $$ %i %e %ev %h1 %h2
    iunfold eventIs at Hx
    icases Hx with ⟨%Hp, -⟩
    ipureintro; exact Hp
  ipureintro; exact ⟨hl, Hall⟩

theorem eventsIs_split (es : List EvModel) (A B : List EvM) :
    eventsIs (GF := GF) es (A ++ B) ⊢
      eventsIs (es.take A.length) A ∗ eventsIs (es.drop A.length) B := by
  unfold eventsIs
  iintro ⟨%hl, #H⟩
  rw [List.length_append] at hl
  isplit
  · isplitr
    · ipureintro; simp only [List.length_take]; omega
    iintro !> %i %e %ev %h1 %h2
    have hi : i < A.length := (List.getElem?_eq_some_iff.1 h2).1
    have h1' : es[i]? = some e := by
      rw [List.getElem?_take_of_lt hi] at h1; exact h1
    iapply H $$ %i %e %ev %h1' %(by rw [List.getElem?_append_left hi]; exact h2)
  · isplitr
    · ipureintro; simp only [List.length_drop]; omega
    iintro !> %i %e %ev %h1 %h2
    rw [List.getElem?_drop] at h1
    iapply H $$ %(A.length + i) %e %ev %h1
      %(by rw [List.getElem?_append_right (by omega)]; simpa using h2)

theorem evsMatch_of_eventsIs (es : List EvModel) (A : List EvM) :
    eventsIs (GF := GF) es A ⊢ evsMatch es (A.map v3rpc.evmToEtcd) := by
  iintro #H
  ihave %Hp := eventsIs_pure es A $$ H
  iunfold eventsIs at H
  icases H with ⟨-, #Hall⟩
  unfold evsMatch
  isplitr
  · ipureintro
    refine ⟨by simp [Hp.1], fun i e c he hc => ?_⟩
    rw [List.getElem?_map] at hc
    cases hai : A[i]? with
    | none => rw [hai] at hc; simp at hc
    | some ev =>
      rw [hai] at hc
      simp only [Option.map_some, Option.some.injEq] at hc
      subst hc
      obtain ⟨h1, h2, h3⟩ := Hp.2 i e ev he hai
      exact ⟨h1, h2, h3⟩
  iintro !> %i %e %c %he %hc
  rw [List.getElem?_map] at hc
  cases hai : A[i]? with
  | none => rw [hai] at hc; simp at hc
  | some ev =>
    rw [hai] at hc
    simp only [Option.map_some, Option.some.injEq] at hc
    subst hc
    ihave Hx := Hall $$ %i %e %ev %he %hai
    iunfold eventIs at Hx
    icases Hx with ⟨-, Hk⟩
    simp only [v3rpc.evmToEtcd]
    iexact Hk

/-! ## A block of events, as a chain of steps -/

/-- **A block of watch events of a log the client saw, as the cache's chain of steps**
(`watchChain`): the delivered events `es` are the watch events of `[b, d)` of the prefix's range
(`d` within the log), no watch event in `[p + 1, b)`: a chain of steps from `p`, one per
revision with events. -/
theorem km_chain (γ : KMNames) (L : Log) (hwf : LogWf' L) (hlen : L.length < 2 ^ 63)
    (pfx : GoString) (rg : WatchRange) (hcov : ∀ k, rg.covers k = true ↔ pfx <+: k) (d : Nat)
    (hd : d ≤ L.length) :
    ∀ (n p b : Nat) (es : List EvModel), d - b = n → p + 1 ≤ b →
      watchEvents L rg (p + 1) b = [] →
      kmLog (GF := GF) γ L ∗ eventsIs es (watchEvents L rg b d) ⊢
        watchChain (EM := etcdModelOfKV γ) pfx (W64 (p : Int)) (splitBatches es)
  | 0, p, b, es, hn, _, _ => by
    rw [watchEvents_empty L rg (show d ≤ b by omega)]
    iintro ⟨-, Hes⟩
    ihave %He := eventsIs_pure es [] $$ Hes
    have : es = [] := List.eq_nil_of_length_eq_zero (by simpa using He.1)
    subst this
    simp only [splitBatches]
    unfold watchChain; itrivial
  | n + 1, p, b, es, hn, hpb, hnone => by
    iintro ⟨#HL, #Hes⟩
    have hsplit := watchEvents_append L rg (show b ≤ b + 1 by omega) (show b + 1 ≤ d by omega)
    by_cases hA : watchEvents L rg b (b + 1) = []
    · have hevs : watchEvents L rg b d = watchEvents L rg (b + 1) d := by
        rw [hsplit, hA, List.nil_append]
      rw [hevs]
      iapply km_chain γ L hwf hlen pfx rg hcov d hd n p (b + 1) es (by omega) (by omega)
        (by rw [watchEvents_append L rg hpb (show b ≤ b + 1 by omega), hnone, hA]; rfl)
      iframe HL Hes
    · have H1 := km_step_of (GF := GF) γ L hwf hlen pfx rg hcov p b (by omega) (by omega) hnone
      generalize hAe : watchEvents L rg b (b + 1) = A at *
      generalize hBe : watchEvents L rg (b + 1) d = B at *
      rw [hsplit]
      ihave %He := eventsIs_pure es (A ++ B) $$ Hes
      ihave ⟨#HA, #HB⟩ := eventsIs_split es A B $$ Hes
      obtain ⟨hl, hpt⟩ := He
      rw [List.length_append] at hl
      have hAmem : ∀ ev ∈ A, ev.kv.modRev = W64 (b : Int) := by
        intro ev hev
        obtain ⟨j, h1, h2, hj⟩ :=
          v3rpc.watchEvents_mem_rev L rg b (b + 1) ev (by rw [hAe]; exact hev)
        rw [hj, show j = b by omega]
      have hrevA : ∀ e ∈ es.take A.length, e.rev = W64 (b : Int) := by
        intro e he
        obtain ⟨i, hi, hei⟩ := List.getElem_of_mem he
        have hiA : i < A.length := by simp only [List.length_take] at hi; omega
        have hie : i < es.length := by simp only [List.length_take] at hi; omega
        have h1 : es[i]? = some e := by
          rw [← hei, List.getElem_take]; exact List.getElem?_eq_getElem hie
        have h2 : (A ++ B)[i]? = some A[i] := by
          rw [List.getElem?_append_left hiA]; exact List.getElem?_eq_getElem hiA
        rw [(hpt i e _ h1 h2).2.2]
        exact hAmem _ (List.getElem_mem _)
      have hrevB : ∀ e, (es.drop A.length).head? = some e → e.rev ≠ W64 (b : Int) := by
        intro e he hr
        rw [List.head?_drop] at he
        obtain ⟨ev, hev⟩ : ∃ ev, B.head? = some ev := by
          cases hB : B with
          | nil =>
            have hlt : A.length < es.length := (List.getElem?_eq_some_iff.1 he).1
            rw [hB] at hl; simp at hl; omega
          | cons ev _ => exact ⟨ev, rfl⟩
        have h2 : (A ++ B)[A.length]? = some ev := by
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          cases B with
          | nil => simp at hev
          | cons b0 bs => simpa using hev
        have := (hpt _ e ev he h2).2.2
        obtain ⟨j, h1, h2', hj⟩ := v3rpc.watchEvents_mem_rev L rg (b + 1) d ev
          (by rw [hBe]; exact List.mem_of_head? hev)
        rw [hr, hj] at this
        have := W64_inj_of_lt (by omega) (by omega) this
        omega
      have hAne' : es.take A.length ≠ [] := by
        intro h
        have := congrArg List.length h
        simp only [List.length_take, List.length_nil] at this
        apply hA; apply List.eq_nil_of_length_eq_zero; omega
      have hsb : splitBatches es = es.take A.length :: splitBatches (es.drop A.length) := by
        have hes := List.take_append_drop A.length es
        calc splitBatches es = splitBatches (es.take A.length ++ es.drop A.length) := by rw [hes]
          _ = _ := km_splitBatches_block (W64 (b : Int)) _ hrevB _ hAne' hrevA
      have hbr : batchRev (es.take A.length) = W64 (b : Int) := by
        cases hz : es.take A.length with
        | nil => exact absurd hz hAne'
        | cons e es' => exact hrevA e (by rw [hz]; exact List.mem_cons_self)
      rw [hsb]
      unfold watchChain
      rw [hbr]
      isplitr
      · unfold etcdStepCertBody
        rw [hbr]
        iexists A.map v3rpc.evmToEtcd
        isplitr
        · iapply evsMatch_of_eventsIs $$ HA
        isplitr
        · rw [etcdModelOfKV_EtcdStep]; iapply H1 $$ HL
        isplitr
        · ipureintro
          intro c hc _
          obtain ⟨ev, hev, rfl⟩ := List.mem_map.1 hc
          rw [← hAe] at hev
          exact (hcov _).1 (List.mem_filter.1 hev).2
        iapply kmLog_reached γ L b (by omega) (by omega) $$ HL
      isplitr
      · ipureintro; word
      have H2 := km_chain γ L hwf hlen pfx rg hcov d hd n b (b + 1) (es.drop A.length)
        (by omega) (by omega) (watchEvents_empty L rg (Nat.le_refl _))
      rw [hBe] at H2
      iapply H2
      iframe HL HB

/-! ## A response, as etcd's -/

theorem km_w64_nat (x : w64) (hx : 0 ≤ sint.Z x) : W64 ((sint.nat x : Nat) : Int) = x := by
  have : ((sint.nat x : Nat) : Int) = sint.Z x := by
    show (((sint.Z x).toNat : Nat) : Int) = _; omega
  rw [this]; word

/-- **A response of a prefix watch, read at a state the client saw, is etcd's** (the cache's
contract, `watchRespOk`, at the adapter's model): an error or a response without events as is; a
progress notification at the watch's start reached by the caller's floor (`etcdReached
(rev - 1)`), else past the cursor a step without events of the state's log through its revision
(`kmStep`, `km_step_of`), reached since the client saw the state; events, the state log's watch
events of the prefix's range (`rangeEvents_take`), a chain of steps (`km_chain`). -/
theorem watchRespOk_of_km (γ : KMNames) (l0 : List (List Change)) (pfx : GoString)
    (hp : pfx ≠ []) (hff : prefixRangeEnd pfx ≠ [W8 0]) (o : OpFull) (rev : w64)
    (hk : o.key = pfx) (he : o.base.rangeEnd = prefixRangeEnd pfx) (hrev : o.base.rev = rev)
    (σ : KVState) (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    kmSeenQ (GF := GF) γ l0 σ ∗ etcdReached (EM := etcdModelOfKV γ) (rev - W64 1) ∗
      watchStateRespOk o σ c c' v r ⊢ watchRespOk (EM := etcdModelOfKV γ) pfx c c' v r := by
  have hcov := pfxRange_cov pfx hp hff
  iintro ⟨#HQ, #Hr0, #Hok⟩
  iunfold kmSeenQ at HQ
  icases HQ with ⟨#Hlb, -⟩
  unfold watchStateRespOk watchRespOk
  icases Hok with (⟨%H, #Hs⟩ | %H | %H | ⟨%H, #Hev⟩)
  · ileft; iframe Hs; ipureintro; exact H
  · iright; ileft; ipureintro; exact H
  · iright; iright; ileft
    obtain ⟨hne, hpn, hc0, hch, hc', hcase⟩ := H
    rcases hcase with ⟨heq, hst⟩ | ⟨hle, hnil, hok⟩
    · -- at the watch's start: the caller's floor
      have hcr : c = r.hdrRev := by word
      have hb : sint.Z o.base.rev < 2 ^ 63 := by word
      isplitr
      · ipureintro; exact ⟨hne, hpn, hch, hc', by omega⟩
      isplitr
      · ileft; ipureintro; exact hcr
      iapply etcdReached_mono (EM := etcdModelOfKV γ) (rev - W64 1) r.hdrRev
        (by rw [← hrev]; word) $$ Hr0
    · -- past the cursor (or at it): the state's log through its revision
      obtain ⟨hl, hrc⟩ := kvLogOkTo_len hok
      have hr1 := hok.2.1
      have h63 := hok.2.2.1
      have hhz : ((sint.nat r.hdrRev : Nat) : Int) = sint.Z r.hdrRev := by
        show (((sint.Z r.hdrRev).toNat : Nat) : Int) = _; omega
      have hcz : ((sint.nat c : Nat) : Int) = sint.Z c := by
        show (((sint.Z c).toNat : Nat) : Int) = _; omega
      have hWh := km_w64_nat r.hdrRev (by omega)
      have hWc := km_w64_nat c hc0
      isplitr
      · ipureintro; exact ⟨hne, hpn, hch, hc', by omega⟩
      isplitr
      · by_cases hcq : sint.Z c = sint.Z r.hdrRev
        · ileft; ipureintro; word
        iright
        have hE := rangeEvents_take σ o pfx hp hff hk he (sint.nat r.hdrRev) hok
          (sint.nat c + 1) (sint.nat r.hdrRev + 1) (by omega) (Nat.le_refl _)
        rw [hnil] at hE
        have hLl : (σ.log.take (sint.nat r.hdrRev + 1)).length = sint.nat r.hdrRev + 1 := by
          rw [List.length_take]; omega
        have hsplit := watchEvents_append (σ.log.take (sint.nat r.hdrRev + 1)) (pfxRange pfx)
          (show sint.nat c + 1 ≤ sint.nat r.hdrRev by omega)
          (show sint.nat r.hdrRev ≤ sint.nat r.hdrRev + 1 by omega)
        rw [← hE] at hsplit
        have hnone := (List.append_eq_nil_iff.1 hsplit.symm).1
        have hlast := (List.append_eq_nil_iff.1 hsplit.symm).2
        ihave #HL := kmLog_take γ σ (sint.nat r.hdrRev) hok $$ Hlb
        have Hs := km_step_of (GF := GF) γ (σ.log.take (sint.nat r.hdrRev + 1)) hok.2.2.2.1
          (by omega) pfx (pfxRange pfx) hcov (sint.nat c) (sint.nat r.hdrRev) (by omega)
          (by omega) hnone
        rw [hlast, hWc, hWh, List.map_nil] at Hs
        rw [etcdModelOfKV_EtcdStep]
        iapply Hs $$ HL
      ihave ⟨#Hre, -⟩ := km_reached_of γ σ.changes (sint.nat r.hdrRev) (by omega) (by omega) $$ Hlb
      iapply etcdReached_mono (EM := etcdModelOfKV γ) _ r.hdrRev
        (Int.le_of_eq (congrArg sint.Z hWh.symm)) $$ Hre
  · -- events: the state log's, a chain of steps
    iright; iright; iright
    obtain ⟨hne, hev0, hc0, hcc, hle, hlast, hok⟩ := H
    obtain ⟨hl, hrc⟩ := kvLogOkTo_len hok
    have hr1 := hok.2.1
    have h63 := hok.2.2.1
    have hcz' : ((sint.nat c' : Nat) : Int) = sint.Z c' := by
      show (((sint.Z c').toNat : Nat) : Int) = _; omega
    have hcz : ((sint.nat c : Nat) : Int) = sint.Z c := by
      show (((sint.Z c).toNat : Nat) : Int) = _; omega
    have hWc := km_w64_nat c hc0
    have hE := rangeEvents_take σ o pfx hp hff hk he (sint.nat c') hok
      (sint.nat c + 1) (sint.nat c' + 1) (by omega) (Nat.le_refl _)
    have hLl : (σ.log.take (sint.nat c' + 1)).length = sint.nat c' + 1 := by
      rw [List.length_take]; omega
    rw [hE]
    ihave %Hp := eventsIs_pure _ _ $$ Hev
    ihave #HL := kmLog_take γ σ (sint.nat c') hok $$ Hlb
    obtain ⟨hlen', hpt⟩ := Hp
    have hmr := map_rev_eq r.events _ hlen' (fun i e ev h1 h2 => (hpt i e ev h1 h2).2.2)
    isplitr
    · ipureintro
      refine ⟨hne, hev0, ?_, ?_, hlast⟩
      · unfold EvRevSorted
        have h1 := km_watchEvents_sorted (σ.log.take (sint.nat c' + 1)) (by omega) (pfxRange pfx)
          (sint.nat c + 1) (sint.nat c' + 1)
        have h2 : (r.events.map EvModel.rev).Pairwise (fun x y => sint.Z x ≤ sint.Z y) := by
          rw [hmr, List.pairwise_map]; exact h1
        exact (List.pairwise_map (f := EvModel.rev) (R := fun x y => sint.Z x ≤ sint.Z y)).1 h2
      · intro e he'
        have hm : e.rev ∈ r.events.map EvModel.rev := List.mem_map_of_mem he'
        rw [hmr] at hm
        obtain ⟨ev, hev, hre⟩ := List.mem_map.1 hm
        obtain ⟨j, hj1, hj2, hj⟩ := v3rpc.watchEvents_mem_rev _ _ _ _ ev hev
        rw [← hre, hj]
        have : sint.Z (W64 (j : Int)) = j := by word
        rw [this]; omega
    have Hc := km_chain (GF := GF) γ (σ.log.take (sint.nat c' + 1)) hok.2.2.2.1 (by omega) pfx
      (pfxRange pfx) hcov (sint.nat c' + 1) (Nat.le_of_eq hLl.symm) _ (sint.nat c)
      (sint.nat c + 1) r.events rfl (Nat.le_refl _) (watchEvents_empty _ _ (Nat.le_refl _))
    rw [hWc] at Hc
    iapply Hc
    iframe HL Hev

/-- **The `i`-th response of a prefix watch with the adapter's read update is etcd's** (the
cache's channel element, `etcdWatchElem`). -/
theorem etcdWatchElem_of_km (γ : KMNames) (l0 : List (List Change)) (pfx : GoString)
    (hp : pfx ≠ []) (hff : prefixRangeEnd pfx ≠ [W8 0]) (o : OpFull) (rev : w64)
    (hk : o.key = pfx) (he : o.base.rangeEnd = prefixRangeEnd pfx) (hrev : o.base.rev = rev)
    (γw : EtcdWatchNames) (Au : IProp GF) (i : Int) (v : go_etcd_io.etcd.client.v3.WatchResponse) :
    etcdReached (EM := etcdModelOfKV γ) (rev - W64 1) ∗
        watchStateElem (GF := GF) γw o (kmSeenQ γ l0) Au i v ⊢
      etcdWatchElem (EM := etcdModelOfKV γ) γw pfx i v := by
  iintro ⟨#Hr0, H⟩
  iunfold watchStateElem at H
  icases H with ⟨%r, %σ, %c, %c', #Hra, #HQ, Hi, Hi', #Hok, -⟩
  unfold etcdWatchElem
  iexists r, c, c'
  iframe Hra Hi Hi'
  iapply watchRespOk_of_km γ l0 pfx hp hff o rev hk he hrev σ c c' v r $$ [HQ Hr0 Hok]
  iframe HQ Hr0 Hok

end ghost

section bridge
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **A client watcher of etcd's KV meets the cache's watcher contract** at the adapter's model
(see the file header), for a prefix not empty and not all `0xff` (`watcher.Watch.spec`'s
prefix-watch condition): the channel `Watch` returns, its elements etcd's
(`etcdWatchElem_of_km`). -/
theorem isEtcdWatcher_of_km (w : Loc) (γ : KMNames) (pfx : GoString) (hp : pfx ≠ [])
    (hff : prefixRangeEnd pfx ≠ [W8 0]) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isKvWatcher w γ.kv ∗ kmInv γ ⊢
    isEtcdWatcher (EM := etcdModelOfKV γ) (watcherIfaceOf w) pfx := by
  iintro ⟨#P1, #P2, #P3, #Hw, #Hinv⟩
  unfold isEtcdWatcher
  iintro !> %ctx %cs %key %sl %gs %rev %Φ !> ⟨#Hctx, #Hopts, %Hpre, #Hrd⟩ HΦ
  obtain ⟨hpw, hnp, hrev⟩ := Hpre
  unfold OpFull.isPrefixWatch at hpw
  simp only [decide_eq_true_eq, hp, if_false] at hpw
  obtain ⟨ht, hr, -, -, hpk, hfr, hfp, hfd, hkey, hend⟩ := hpw
  ihave #Hreach := etcdRead_reached (EM := etcdModelOfKV γ) (rev - W64 1) $$ Hrd
  imod km_reached_lb γ (rev - W64 1) $$ Hreach with ⟨%l0, #Hl0, -⟩
  ihave #Hau := km_read_au γ l0 $$ [$Hinv $Hl0]
  -- (G2) the watcher's environment explicit, no auth bound (`n = 0`)
  ihave #Hw' := Hw
  iunfold isKvWatcher at Hw'
  icases Hw' with ⟨%V, #Hcw, %Hkst⟩
  iapply (v3.watcher.wp_Watch w V γ.kv ctx cs key sl gs rev (kmSeenQ γ l0) 0) $$ [] [HΦ]
  · iframe #
    isplitr
    · ipureintro; exact Hkst
    isplitr
    · ipureintro
      refine ⟨?_, hnp, by omega⟩
      unfold OpFull.isRangeWatch; simp only [decide_eq_true_eq]
      exact ⟨ht, hr, hpk, hfr, hfp, hfd⟩
    isplitr
    · iintro !> %h
      exact absurd h.2 (Nat.lt_irrefl 0)
    iunfold kvReadAu at Hau
    iunfold kvAu at Hau
    iexact Hau
  inext
  iintro %ch %γw ⟨#Hs, Hc, Hi⟩
  iapply HΦ
  isplitr
  · unfold isEtcdWatchChan
    iexists watchStateElem γw (opWatchModel key gs) (kmSeenQ γ l0) _
    iframe Hs
    iintro !> %i %v H
    imodintro
    iapply etcdWatchElem_of_km γ l0 pfx hp hff (opWatchModel key gs) rev hkey hend hr γw _ i v
      $$ [Hreach H]
    iframe Hreach H
  unfold etcdWatchConsumer
  iexists []
  iframe Hc Hi
  ipureintro; rfl

/-- **A client watcher of etcd's KV is the cache's progress notifier** (`isKvWatcher`'s client
watcher, `isEtcdProgressNotifier_of_watcher`). -/
theorem isEtcdProgressNotifier_of_km (w : Loc) (γk : KVNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isKvWatcher w γk ⊢
    isEtcdProgressNotifier (watcherIfaceOf w) := by
  iintro ⟨#P1, #P2, #P3, #Hw⟩
  iunfold isKvWatcher at Hw
  icases Hw with ⟨%V, #Hcw, -⟩
  iapply isEtcdProgressNotifier_of_watcher v3.watcher.wp_RequestProgress V w $$ [P1 P2 P3 Hcw]
  iframe #

end bridge

end client
end EtcdGrove
end Perennial
