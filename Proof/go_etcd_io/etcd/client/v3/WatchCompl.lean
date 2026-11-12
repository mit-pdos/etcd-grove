/-
**A watch's completeness, as the cache's contract states it** (the watch slice's unit W-K, K2e-7):
from mvcc's watch events of a certified log (strict M1: a member's `histLb`) to the cache's chain of steps (`watchChain`,
`cache/v3/InvEtcd.lean`), for a watch whose range covers exactly the keys under a prefix. Lean-first,
no Rocq counterpart.

* `splitBatches_head`, `splitBatches_block`: a leading block of one revision's events, followed by
  later ones, is the first batch.
* `watchChain_of_watch`: the watch events of the revisions `[b, d)` of a certified log, with no
  watch event in `[p + 1, b)`, are a chain of steps from `p`, batch by batch.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.WatchContent
public import Proof.go_etcd_io.etcd.client.v3.PrefixRange

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open mvcc txn

/-! ## Batches -/

/-- The first batch's revision is the first event's. -/
theorem splitBatches_head : ∀ B : List EvModel,
    (splitBatches B).head?.map batchRev = B.head?.map EvModel.rev
  | [] => rfl
  | e :: es => by
    unfold splitBatches
    split
    · rfl
    · split <;> rfl

/-- **A leading block of one revision** `x`'s events, followed by events not starting at `x`, is
the first batch. -/
theorem splitBatches_block (x : w64) (B : List EvModel)
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
          have h1 := splitBatches_head (b :: bs)
          rw [hs] at h1; simp at h1
      subst this; rfl
    | cons b bs =>
      have h1 := splitBatches_head B
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
    have ih := splitBatches_block x B hB (e' :: A') (by simp)
      (fun y hy => hA y (List.mem_cons_of_mem _ hy))
    show splitBatches (e :: (e' :: A' ++ B)) = (e :: e' :: A') :: splitBatches B
    rw [splitBatches.eq_2, show e' :: A' ++ B = e' :: (A' ++ B) from rfl] at *
    rw [ih]
    have h1 : batchRev (e' :: A') = e.rev := by
      show e'.rev = e.rev
      rw [hA e' (List.mem_cons_of_mem _ List.mem_cons_self), hA e List.mem_cons_self]
    simp only [h1, ↓reduceIte]

/-! ## The prefix watch's range -/

/-- **A prefix watch's registered range covers exactly the keys under its key** (a non-empty key,
not all `0xff`: its range end is neither empty nor `[0]`). -/
theorem covers_prefix (c : v3rpc.CreateReqM) (id : w64) (r : WatchRange)
    (hc : v3rpc.createRangeOk c id r) (hkey : c.key ≠ []) (hend : c.rangeEnd = prefixRangeEnd c.key)
    (hff : prefixRangeEnd c.key ≠ [W8 0]) : ∀ k, r.covers k = true ↔ c.key <+: k := by
  intro k
  rw [← concurrency.inRange_prefix c.key k hkey, ← hend]
  obtain ⟨hk, -, -, he⟩ := hc
  rw [if_neg hkey] at hk
  have h0 : c.rangeEnd ≠ [] := by rw [hend]; exact concurrency.prefixRangeEnd_ne_nil _
  have h1 : c.rangeEnd ≠ [W8 0] := by rw [hend]; exact hff
  rw [if_neg h0, if_neg h1] at he
  unfold WatchRange.covers inRange
  rw [he, if_neg h0, if_neg h1, hk]
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, adt.affCmp_nonneg_iff, adt.affCmp_neg_iff, adt.affLt]
  by_cases hk0 : k = go!""
  · subst hk0
    have hlt : go.GoStringLt [] c.key := by
      obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil hkey
      rw [ht]; exact go.goStringLt_nil_cons a t
    simp [hlt]
  · simp [hk0, hkey, h0]

/-- **A point watch is registered exactly** (G2, 2026-10-30). -/
theorem rangeExact_point (key : GoString) : rangeExact key [] := by
  intro c id r hck hce hc k
  obtain ⟨hk, -, -, he⟩ := hc
  rw [hck] at hk
  rw [hce, if_pos rfl] at he
  unfold WatchRange.covers inRange
  rw [he, hk]
  simp

/-- **A proper range of a non-empty key is registered exactly** (G2, 2026-10-30): its range end
neither empty nor `[0]` (a prefix watch's, `prefixRangeEnd`, of a key not all `0xff`, included). -/
theorem rangeExact_proper (key ed : GoString) (hkey : key ≠ []) (h0 : ed ≠ [])
    (h1 : ed ≠ [W8 0]) : rangeExact key ed := by
  intro c id r hck hce hc k
  obtain ⟨hk, -, -, he⟩ := hc
  rw [hck] at hk
  rw [hce, if_neg h0, if_neg h1] at he
  unfold WatchRange.covers inRange
  rw [he, if_neg h0, if_neg h1, hk]
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, adt.affCmp_nonneg_iff, adt.affCmp_neg_iff, adt.affLt]
  by_cases hk0 : k = go!""
  · subst hk0
    have hlt : go.GoStringLt [] key := by
      obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil hkey
      rw [ht]; exact go.goStringLt_nil_cons a t
    simp [hlt]
  · simp [hk0, hkey, h0]

/-- **A from-key range of a non-empty key is registered exactly** (G2, 2026-10-30): the range end
`[0]` is registered open-ended (`createRangeOk`'s `some []`). -/
theorem rangeExact_fromKey (key : GoString) (hkey : key ≠ []) : rangeExact key [W8 0] := by
  intro c id r hck hce hc k
  obtain ⟨hk, -, -, he⟩ := hc
  rw [hck] at hk
  rw [hce, if_neg (by simp), if_pos rfl] at he
  rw [mvcc.covers_from r k he (by rw [hk]; exact hkey), hk, inRange_from]

/-- **Every range of a non-empty key is registered exactly** (G2, 2026-10-30): a point, a from-key
range or a proper range. -/
theorem rangeExact_of_ne (key ed : GoString) (hkey : key ≠ []) : rangeExact key ed := by
  by_cases h0 : ed = []
  · subst h0; exact rangeExact_point key
  by_cases h1 : ed = [W8 0]
  · subst h1; exact rangeExact_fromKey key hkey
  exact rangeExact_proper key ed hkey h0 h1

/-! ## The second cursor's steps (pure) -/

/-- A registered range covering exactly the watch's range: its watch events are the watch's
range events of the log. -/
theorem rangeLogEvents_watchEvents (L : Log) (o : OpFull) (rg : WatchRange)
    (hcov : ∀ k, rg.covers k = inRange o.key o.base.rangeEnd k) (lo hi : Nat) :
    rangeLogEvents L o lo hi = watchEvents L rg lo hi := by
  unfold rangeLogEvents watchEvents
  congr 1
  funext ev
  rw [hcov]

/-- A sub-block of an empty block of watch events is empty. -/
theorem watchEvents_sub_nil (L : Log) (rg : WatchRange) {a b x y : Nat} (h : watchEvents L rg a b = [])
    (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) : watchEvents L rg x y = [] := by
  rw [watchEvents_append L rg hax (show x ≤ b by omega),
    watchEvents_append L rg hxy hyb] at h
  exact (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 h).2).1

/-- The events up to `q + 1` of the cursor's log, on another log of the store (in prefix order
with it) that has them or when there are none (`q + 1 = lo`). -/
theorem cut_transfer (L L' : Log) (hc : L <+: L' ∨ L' <+: L) (rg : WatchRange) (lo q : Nat)
    (hq : q + 1 ≤ L.length ∨ q + 1 = lo) (hq' : q + 1 ≤ L'.length) :
    watchEvents L rg lo (q + 1) = watchEvents L' rg lo (q + 1) := by
  rcases hq with hq | hq
  · rcases hc with hc | hc
    · exact watchEvents_prefix hc rg hq
    · exact (watchEvents_prefix hc rg hq').symm
  · rw [hq, watchEvents_empty L rg (Nat.le_refl _), watchEvents_empty L' rg (Nat.le_refl _)]

/-- **The events of a response, from the second cursor**: the events so far `E` up to the cursor
`q` (`q + 1` within the cursor's log `L`, or `lo`), then the response's `evs` (non-empty), the
watch events `[lo, d)` of a log `L2` of the store: `evs` are those of `[q + 1, d)`. -/
theorem cmpl_events_cut (L L2 : Log) (hc : L <+: L2 ∨ L2 <+: L) (rg : WatchRange) (lo q d : Nat)
    (E evs : List EvM) (h1 : E = watchEvents L rg lo (q + 1)) (hlo : lo ≤ q + 1)
    (hq : q + 1 ≤ L.length ∨ q + 1 = lo)
    (h2 : E ++ evs = watchEvents L2 rg lo d) (hd : d ≤ L2.length ∨ d ≤ lo) (hne : evs ≠ []) :
    q + 1 ≤ d ∧ d ≤ L2.length ∧ evs = watchEvents L2 rg (q + 1) d := by
  have hlod : lo < d := by
    refine Classical.byContradiction fun hc' => ?_
    rw [watchEvents_empty L2 rg (show d ≤ lo by omega)] at h2
    exact hne (List.append_eq_nil_iff.1 h2).2
  have hdL2 : d ≤ L2.length := hd.resolve_right (by omega)
  have hq2 : q + 1 ≤ L2.length := by
    refine Classical.byContradiction fun hn => ?_
    -- the cursor past `L2`: then `L2 <+: L` and the response's events would be before the cursor
    have hqL : q + 1 ≤ L.length := hq.resolve_right (by omega)
    have hpre : L2 <+: L := by
      rcases hc with hc | hc
      · exact absurd (Nat.le_trans hqL hc.length_le) hn
      · exact hc
    rw [watchEvents_prefix hpre rg hdL2] at h2
    rw [h1, watchEvents_append L rg (Nat.le_of_lt hlod) (show d ≤ q + 1 by omega),
      List.append_assoc] at h2
    have := congrArg List.length h2
    simp only [List.length_append] at this
    exact hne (List.eq_nil_of_length_eq_zero (by omega))
  rw [h1, cut_transfer L L2 hc rg lo q hq hq2] at h2
  rcases v3rpc.watchEvents_mid L2 rg lo (q + 1) d evs hlo h2 with h | ⟨h3, h4⟩
  · exact absurd h hne
  · exact ⟨h3, hdL2, h4⟩

/-- **The second cursor after events**: the last event's revision `q'` (above the cursor `q`,
below `d`), no event after it before `d`. -/
theorem cmpl_events_last (L : Log) (hlen : L.length < 2 ^ 63) (rg : WatchRange) (q d : Nat)
    (evs : List EvM) (hev : evs = watchEvents L rg (q + 1) d) (hne : evs ≠ []) (hd : d ≤ L.length) :
    ∃ q' : Nat, evs.getLast?.map (fun e => e.kv.modRev) = some (W64 (q' : Int)) ∧ q + 1 ≤ q' ∧
      q' < d ∧ watchEvents L rg (q' + 1) d = [] ∧
      ∀ e ∈ evs, ∃ j : Nat, q + 1 ≤ j ∧ j < d ∧ e.kv.modRev = W64 (j : Int) := by
  have hmem : ∀ e ∈ evs, ∃ j : Nat, q + 1 ≤ j ∧ j < d ∧ e.kv.modRev = W64 (j : Int) := by
    intro e he; rw [hev] at he; exact v3rpc.watchEvents_mem_rev L rg (q + 1) d e he
  obtain ⟨e, he⟩ : ∃ e, evs.getLast? = some e := by
    cases h : evs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
    | some e => exact ⟨e, rfl⟩
  obtain ⟨j, hj1, hj2, hj⟩ := hmem e (List.mem_of_getLast? he)
  refine ⟨j, by rw [he]; simp [hj], hj1, hj2, ?_, hmem⟩
  have hsplit := watchEvents_append L rg (show q + 1 ≤ j + 1 by omega) (show j + 1 ≤ d by omega)
  rw [← hev] at hsplit
  refine Classical.byContradiction fun hT => ?_
  have hl : (watchEvents L rg (j + 1) d).getLast? = some e := by
    rw [hsplit, List.getLast?_append] at he
    cases h' : (watchEvents L rg (j + 1) d).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 h') hT
    | some e' => rw [h'] at he; simpa using he
  obtain ⟨j', hj'1, hj'2, hj'⟩ := v3rpc.watchEvents_mem_rev L rg (j + 1) d e (List.mem_of_getLast? hl)
  rw [hj] at hj'
  have := W64_inj_of_lt (by omega) (by omega) hj'
  omega

/-- **No event of the range in `(q, p]`**: the events so far end at the cursor `q` and, by the
progress notification's coverage, at `p` (`q ≤ p`, `p + 1` within the log `Lp`). -/
theorem cmpl_prog_none (L Lp : Log) (hc : L <+: Lp ∨ Lp <+: L) (rg : WatchRange) (lo q p : Nat)
    (hlo : lo ≤ q + 1) (hq : q + 1 ≤ L.length ∨ q + 1 = lo) (hp : p + 1 ≤ Lp.length) (hqp : q ≤ p)
    (h : watchEvents L rg lo (q + 1) = watchEvents Lp rg lo (p + 1)) :
    watchEvents Lp rg (q + 1) (p + 1) = [] := by
  rw [cut_transfer L Lp hc rg lo q hq (by omega),
    watchEvents_append Lp rg (lo := lo) (mid := q + 1) (hi := p + 1) hlo (by omega)] at h
  have := congrArg List.length h
  simp only [List.length_append] at this
  exact List.eq_nil_of_length_eq_zero (by omega)

/-! ## The chain of steps of a block of watch events -/

section chain
open Iris Iris.BI Iris.ProofMode
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

open Iris Iris.BI Iris.ProofMode

/-- **A step's pure facts at a well-formed log, from its watch events** (W3: `srvStep_of_watch`'s
pure part, `stepPure`). -/
theorem stepPure_of_watch (log : mvcc.Log) (rng : mvcc.WatchRange) (pfx : GoString)
    (hcov : ∀ k, rng.covers k = true ↔ pfx <+: k) (r0 r1 : Nat) (h01 : r0 ≤ r1)
    (h1 : r1 < log.length) (hwf : mvcc.LogWf' log) (hlen : log.length < 2 ^ 63)
    (hnone : ∀ x : Nat, r0 < x → x < r1 → mvcc.watchEvents log rng x (x + 1) = []) :
    stepPure log (W64 (r0 : Int)) (W64 (r1 : Int)) pfx
      ((mvcc.watchEvents log rng r1 (r1 + 1)).map v3rpc.evmToEtcd) := by
  obtain ⟨hz, hs⟩ := v3rpc.watchStreamSpec_step log hwf hlen rng pfx hcov r0 r1 hnone
  have e0 : sint.Z (W64 (r0 : Int)) = r0 := by word
  have e1 : sint.Z (W64 (r1 : Int)) = r1 := by word
  refine ⟨by omega, by omega, by omega, fun x hx1 hx2 => hz x (by omega) (by omega), ?_⟩
  rw [e1]
  simpa using hs

/-- **One revision's watch events, as one batch's step** (`etcdStepCertBody`): from `p` to `b`,
no watch event in `[p + 1, b)`, the events of `b` (with their key-values read-only at `kvs`). -/
theorem stepCert_of_watch (V : WEnv GF) (L : mvcc.Log) (rg : mvcc.WatchRange) (pfx : GoString)
    (hcov : ∀ k, rg.covers k = true ↔ pfx <+: k) (p b : Nat) (hpb : p + 1 ≤ b) (hb : b < L.length)
    (hnone : mvcc.watchEvents L rg (p + 1) b = []) (kvs : List Loc)
    (hkl : kvs.length = (mvcc.watchEvents L rg b (b + 1)).length)
    (hAne : mvcc.watchEvents L rg b (b + 1) ≠ []) :
    □ V.W.histLb L ∗ srvWLaws V.W ∗
      □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc), ⌜(mvcc.watchEvents L rg b (b + 1))[k]? = some ev⌝ →
        ⌜kvs[k]? = some kv⌝ → mvcc.kvPtrFixed kv ev.kv) ∗ □ V.WL L ∗ watchLaws V ⊢
      etcdStepCertBody (EM := V.WM) pfx (W64 (p : Int))
        (List.zipWith evModelOf (mvcc.watchEvents L rg b (b + 1)) kvs) := by
  iintro ⟨#HL, #Hsm, #Hkv, #HWL, #Hlaws⟩
  iunfold watchLaws at Hlaws
  icases Hlaws with ⟨#Hlr, -, #Hlst, -⟩
  ihave %Hw := srvWLaws_model V.W L $$ [$Hsm $HL]
  have hlen : L.length < 2 ^ 63 := Hw.2.1
  have hnone' : ∀ x : Nat, p < x → x < b → mvcc.watchEvents L rg x (x + 1) = [] := by
    intro x h1 h2
    have := hnone
    rw [mvcc.watchEvents_append L rg (show p + 1 ≤ x by omega) (show x ≤ b by omega),
      mvcc.watchEvents_append L rg (show x ≤ x + 1 by omega) (show x + 1 ≤ b by omega)] at this
    exact (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 this).2).1
  ihave #Hstep := Hlst $$ %L %_ %_ %pfx %_ HWL
    %(stepPure_of_watch L rg pfx hcov p b (by omega) hb Hw.1 hlen hnone')
  generalize hA : mvcc.watchEvents L rg b (b + 1) = A at *
  unfold etcdStepCertBody
  iexists A.map v3rpc.evmToEtcd
  have hbr : batchRev (List.zipWith evModelOf A kvs) = W64 (b : Int) := by
    cases hAe : A with
    | nil => exact absurd hAe hAne
    | cons ev evs =>
      cases kvs with
      | nil => rw [hAe] at hkl; simp at hkl
      | cons kv kvs' =>
        show ev.kv.modRev = _
        have hm : ev ∈ mvcc.watchEvents L rg b (b + 1) := by rw [hA, hAe]; exact List.mem_cons_self
        obtain ⟨j, h1, h2, hj⟩ := v3rpc.watchEvents_mem_rev L rg b (b + 1) ev hm
        have : j = b := by omega
        rw [hj, this]
  isplitr
  · unfold evsMatch
    isplitr
    · ipureintro
      refine ⟨by simp [hkl], fun i e c he hc => ?_⟩
      rw [List.getElem?_zipWith] at he
      rw [List.getElem?_map] at hc
      cases hai : A[i]? with
      | none => rw [hai] at he; simp at he
      | some ev =>
        cases hki : kvs[i]? with
        | none => rw [hai, hki] at he; simp at he
        | some kv =>
          rw [hai, hki] at he; rw [hai] at hc
          simp only [Option.map_some, Option.some.injEq] at he hc
          subst he; subst hc
          exact ⟨rfl, rfl, rfl⟩
    iintro !> %i %e %c %he %hc
    rw [List.getElem?_zipWith] at he
    rw [List.getElem?_map] at hc
    cases hai : A[i]? with
    | none => rw [hai] at he; simp at he
    | some ev =>
      cases hki : kvs[i]? with
      | none => rw [hai, hki] at he; simp at he
      | some kv =>
        rw [hai, hki] at he; rw [hai] at hc
        simp only [Option.map_some, Option.some.injEq] at he hc
        subst he; subst hc
        ihave #Hk := Hkv $$ %i %ev %kv %hai %hki
        ihave ⟨#Hv, -⟩ := kvPtrFixed_facts kv ev.kv $$ Hk
        simp only [evModelOf, v3rpc.evmToEtcd]
        iexact Hv
  isplitr
  · rw [hbr]; iexact Hstep
  isplitr
  · ipureintro
    intro c hc _
    obtain ⟨ev, hev, rfl⟩ := List.mem_map.1 hc
    rw [← hA] at hev
    exact (hcov _).1 (List.mem_filter.1 hev).2
  rw [hbr]
  iapply Hlr $$ %L %(W64 (b : Int)) HWL %(by word)

/-- **A block of watch events as the cache's chain of steps** (`watchChain`): the watch events of
`[b, d)` of a sealed log (`d` within it), a range covering exactly the keys under `pfx`, no watch
event in `[p + 1, b)`: a chain of steps from `p`, one per revision with events. -/
theorem watchChain_of_watch (V : WEnv GF) (L : mvcc.Log) (rg : mvcc.WatchRange) (pfx : GoString)
    (hcov : ∀ k, rg.covers k = true ↔ pfx <+: k) (d : Nat) (hd : d ≤ L.length) :
    ∀ (n p b : Nat) (kvs : List Loc), d - b = n → p + 1 ≤ b →
      mvcc.watchEvents L rg (p + 1) b = [] →
      kvs.length = (mvcc.watchEvents L rg b d).length →
      □ V.W.histLb L ∗ srvWLaws V.W ∗
        □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc), ⌜(mvcc.watchEvents L rg b d)[k]? = some ev⌝ →
          ⌜kvs[k]? = some kv⌝ → mvcc.kvPtrFixed kv ev.kv) ∗ □ V.WL L ∗ watchLaws V ⊢
      watchChain (EM := V.WM) pfx (W64 (p : Int))
        (splitBatches (List.zipWith evModelOf (mvcc.watchEvents L rg b d) kvs))
  | 0, p, b, kvs, hn, _, _, _ => by
    rw [mvcc.watchEvents_empty L rg (show d ≤ b by omega)]
    iintro -
    simp only [List.zipWith_nil_left, splitBatches]
    unfold watchChain; itrivial
  | n + 1, p, b, kvs, hn, hpb, hnone, hkl => by
    iintro ⟨#HL, #Hsm, #Hkv, #HWL, #Hlaws⟩
    ihave %Hw := srvWLaws_model V.W L $$ [$Hsm $HL]
    have hlen : L.length < 2 ^ 63 := Hw.2.1
    have hsplit := mvcc.watchEvents_append L rg (show b ≤ b + 1 by omega) (show b + 1 ≤ d by omega)
    by_cases hA : mvcc.watchEvents L rg b (b + 1) = []
    · -- no event at `b`: on to `b + 1`, from the same `p`
      have hevs : mvcc.watchEvents L rg b d = mvcc.watchEvents L rg (b + 1) d := by
        rw [hsplit, hA, List.nil_append]
      rw [hevs] at hkl ⊢
      iapply watchChain_of_watch V L rg pfx hcov d hd n p (b + 1) kvs (by omega) (by omega)
        (by rw [mvcc.watchEvents_append L rg hpb (show b ≤ b + 1 by omega), hnone, hA]; rfl) hkl
      iframe HL Hsm HWL Hlaws
      iintro !> %k %ev %kv %h1 %h2
      iapply Hkv $$ %k %ev %kv %h1 %h2
    · -- the events at `b`: the first batch, then the rest from `b`
      generalize hAe : mvcc.watchEvents L rg b (b + 1) = A at *
      generalize hBe : mvcc.watchEvents L rg (b + 1) d = B at *
      have hkl' : kvs.length = A.length + B.length := by rw [hkl, hsplit, List.length_append]
      have hkvs : kvs = kvs.take A.length ++ kvs.drop A.length := (List.take_append_drop _ _).symm
      have hzip : List.zipWith evModelOf (A ++ B) kvs =
          List.zipWith evModelOf A (kvs.take A.length) ++
            List.zipWith evModelOf B (kvs.drop A.length) := by
        calc List.zipWith evModelOf (A ++ B) kvs
            = List.zipWith evModelOf (A ++ B) (kvs.take A.length ++ kvs.drop A.length) := by
              rw [List.take_append_drop]
          _ = _ := List.zipWith_append (by simp [hkl'])
      have hrevA : ∀ e ∈ List.zipWith evModelOf A (kvs.take A.length), e.rev = W64 (b : Int) := by
        intro e he
        obtain ⟨ev, hev, hr⟩ := mem_zipWith_evModel he
        rw [hr]
        obtain ⟨j, h1, h2, hj⟩ := v3rpc.watchEvents_mem_rev L rg b (b + 1) ev (by rw [hAe]; exact hev)
        rw [hj, show j = b by omega]
      have hrevB : ∀ e, (List.zipWith evModelOf B (kvs.drop A.length)).head? = some e →
          e.rev ≠ W64 (b : Int) := by
        intro e he hr
        obtain ⟨ev, hev, hr'⟩ := mem_zipWith_evModel (List.mem_of_head? he)
        obtain ⟨j, h1, h2, hj⟩ := v3rpc.watchEvents_mem_rev L rg (b + 1) d ev (by rw [hBe]; exact hev)
        rw [hr', hj] at hr
        have := W64_inj_of_lt (by omega) (by omega) hr
        omega
      have hAne' : List.zipWith evModelOf A (kvs.take A.length) ≠ [] := by
        intro h
        have := congrArg List.length h
        simp only [List.length_zipWith, List.length_take, List.length_nil] at this
        apply hA
        apply List.eq_nil_of_length_eq_zero
        omega
      rw [hsplit, hzip, splitBatches_block (W64 (b : Int)) _ hrevB _ hAne' hrevA]
      have hbr : batchRev (List.zipWith evModelOf A (kvs.take A.length)) = W64 (b : Int) := by
        cases hz : List.zipWith evModelOf A (kvs.take A.length) with
        | nil => exact absurd hz hAne'
        | cons e es => exact hrevA e (by rw [hz]; exact List.mem_cons_self)
      unfold watchChain
      rw [hbr]
      isplitr
      · have H1 := stepCert_of_watch V L rg pfx hcov p b hpb (by omega) hnone (kvs.take A.length)
          (by rw [hAe]; simp [hkl']) (by rw [hAe]; exact hA)
        rw [hAe] at H1
        iapply H1
        iframe HL Hsm HWL Hlaws
        iintro !> %k %ev %kv %h1 %h2
        iapply Hkv $$ %k %ev %kv
          %(by rw [List.getElem?_append_left (by
              rw [List.getElem?_take] at h2; split at h2
              · exact (List.getElem?_eq_some_iff.1 h1).1
              · cases h2)]; exact h1)
          %(by rw [List.getElem?_take] at h2; split at h2
               · exact h2
               · cases h2)
      isplitr
      · ipureintro; word
      have H2 := watchChain_of_watch V L rg pfx hcov d hd n b (b + 1) (kvs.drop A.length)
        (by omega) (by omega) (mvcc.watchEvents_empty L rg (Nat.le_refl _)) (by rw [hBe]; simp [hkl'])
      rw [hBe] at H2
      iapply H2
      iframe HL Hsm HWL Hlaws
      iintro !> %k %ev %kv %h1 %h2
      rw [List.getElem?_drop] at h2
      iapply Hkv $$ %(A.length + k) %ev %kv
        %(by rw [List.getElem?_append_right (by omega)]; simpa using h1) %h2

/-! ## The second cursor -/

/-- **The second cursor's log** (persistent; strict M1): none (`[]`: the watch's start, no event
yet) or a certified lower bound of the member's notified log (in place of mvcc's sealed `evLog`,
whose `[]` was free). -/
def cLog (W : v3rpc.SrvW GF) (L : mvcc.Log) : IProp GF := iprop(⌜L = []⌝ ∨ □ W.histLb L)

instance cLog_persistent (W : v3rpc.SrvW GF) (L : mvcc.Log) : Persistent (cLog W L) := by
  unfold cLog; infer_instance

/-- Two cursor logs are prefix-comparable (`srvWLaws`'). -/
theorem cLog_cmp (W : v3rpc.SrvW GF) (L L' : mvcc.Log) :
    srvWLaws W ∗ cLog W L ∗ □ W.histLb L' ⊢ ⌜L <+: L' ∨ L' <+: L⌝ := by
  iintro ⟨#Hl, #HL, #HL'⟩
  iunfold cLog at HL
  icases HL with (%h | #HL)
  · subst h; ipureintro; left; exact List.nil_prefix
  iunfold srvWLaws at Hl
  icases Hl with ⟨-, #Hc, -⟩
  iapply Hc $$ %L %L' HL HL'

/-- **A response's place in the run's received list** (persistent; strict M1, in place of mvcc's
channel snapshot `chanPos`): the send loop of the run the stream's auxiliary name publishes had
received `pre`, then `y`. -/
def rcvAt (γs : StreamNames) (pre : List mvcc.api.WResp) (y : mvcc.api.WResp) : IProp GF :=
  iprop(∃ r : v3rpc.WRun GF, streamAuxIs γs (v3rpc.auxOf r) ∗ v3rpc.rcvLb r.γr (pre ++ [y]))

instance rcvAt_persistent (γs : StreamNames) (pre : List mvcc.api.WResp) (y : mvcc.api.WResp) :
    Persistent (rcvAt (GF := GF) γs pre y) := by
  unfold rcvAt; infer_instance

/-- **The second cursor at a progress notification's revision** (persistent): `c2` is the
revision of an event-less mvcc response `y` (the `ny`-th the run received), the `i`th of the
responses `Dm` received, sent while the id `X` was live, at its place in the received list. -/
def progAt (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (X c2 : w64) : IProp GF :=
  iprop(∃ (i : Nat) (my : v3rpc.WatchRespM) (y : mvcc.api.WResp) (prey : List mvcc.api.WResp),
    ⌜Dm[i]? = some my ∧ my.src = some (prey.length, y) ∧ y.evs = [] ∧ c2 = y.rev ∧
      v3rpc.idLive (Dm.take i) X⌝ ∗
    rcvAt γs prey y)

instance progAt_persistent (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (X c2 : w64) :
    Persistent (progAt (GF := GF) γs Dm X c2) := by
  unfold progAt; infer_instance

theorem progAt_mono (γs : StreamNames) {Dm Dm' : List v3rpc.WatchRespM} (X c2 : w64)
    (hp : Dm <+: Dm') : progAt (GF := GF) γs Dm X c2 ⊢ progAt γs Dm' X c2 := by
  unfold progAt
  iintro ⟨%i, %my, %y, %prey, %H, #Hp⟩
  obtain ⟨t, rfl⟩ := hp
  have hi : i < Dm.length := (List.getElem?_eq_some_iff.1 H.1).1
  iexists i, my, y, prey
  iframe Hp
  ipureintro
  rw [List.getElem?_append_left hi, List.take_append_of_le_length (Nat.le_of_lt hi)]
  exact H

/-- **The second dispatch cursor `c2` of a registered substream** (persistent; its id `X`, range
`rg`, first revision `lo`, the responses `Dm` received): the events so far are the watch events
`[lo, q + 1)` of a cursor log (`c2 = q`; `q + 1` within it, or `lo`), and `c2` is the watch's
start, the last event's revision, or a progress notification's (`progAt`). -/
def cur2Ok (V : WEnv GF) (γs : StreamNames) (rr : w64) (Dm : List v3rpc.WatchRespM) (X : w64)
    (rg : mvcc.WatchRange) (lo : Nat) (c2 : w64) : IProp GF :=
  iprop((∃ (L : mvcc.Log) (q : Nat), cLog V.W L ∗
      ⌜c2 = W64 (q : Int) ∧ evsOf Dm X = mvcc.watchEvents L rg lo (q + 1) ∧ lo ≤ q + 1 ∧
        (q + 1 ≤ L.length ∨ q + 1 = lo) ∧ q + 1 < 2 ^ 63⌝) ∗
    (⌜c2 = rr - W64 1⌝ ∨ ⌜∃ e, (evsOf Dm X).getLast? = some e ∧ c2 = e.kv.modRev⌝ ∨
      progAt γs Dm X c2))

instance cur2Ok_persistent (V : WEnv GF) (γs : StreamNames) (rr : w64)
    (Dm : List v3rpc.WatchRespM) (X : w64) (rg : mvcc.WatchRange) (lo : Nat) (c2 : w64) :
    Persistent (cur2Ok V γs rr Dm X rg lo c2) := by
  unfold cur2Ok; infer_instance

/-- `cur2Ok` over more responses, none of the watcher's events. -/
theorem cur2Ok_mono (V : WEnv GF) (γs : StreamNames) (rr : w64) {Dm Dm' : List v3rpc.WatchRespM}
    (X : w64) (rg : mvcc.WatchRange) (lo : Nat) (c2 : w64) (h : evsOf Dm' X = evsOf Dm X)
    (hp : Dm <+: Dm') :
    cur2Ok (GF := GF) V γs rr Dm X rg lo c2 ⊢ cur2Ok V γs rr Dm' X rg lo c2 := by
  unfold cur2Ok
  rw [h]
  iintro ⟨#H1, (#H2 | #H2 | #H2)⟩
  · iframe H1; ileft; iexact H2
  · iframe H1; iright; ileft; iexact H2
  · iframe H1; iright; iright; iapply progAt_mono γs X c2 hp $$ H2

/-- **The second cursor at the watch's start** `rev - 1` (`rev ≥ 1`, the first revision `lo`
the start revision), no events yet. -/
theorem cur2Ok_init (V : WEnv GF) (γs : StreamNames) (rr : w64) (Dm : List v3rpc.WatchRespM)
    (X : w64) (rg : mvcc.WatchRange) (lo : Nat) (hrev : 1 ≤ sint.Z rr)
    (hlo : lo = (sint.Z rr).toNat) (hE : evsOf Dm X = []) :
    ⊢ cur2Ok (GF := GF) V γs rr Dm X rg lo (rr - W64 1) := by
  unfold cur2Ok
  isplitr
  · iexists [], (sint.Z rr).toNat - 1
    isplitr
    · unfold cLog; ileft; ipureintro; rfl
    ipureintro
    have h1 : ((sint.Z rr).toNat - 1 : Nat) + 1 = (sint.Z rr).toNat := by omega
    refine ⟨by word, ?_, by omega, Or.inr (by omega), by word⟩
    rw [hE, h1, ← hlo, mvcc.watchEvents_empty _ _ (Nat.le_refl _)]
  ileft; ipureintro; rfl

/-- **The second cursor over a response with events** `evs` (the watcher's: the events so far
then `evs` are the watch events `[lo, d)` of a certified log `L2`; their key-values read-only at
`kvs`): the server-level contract from `c2` (events, `rawRespOk`: `L2`'s range events from `c2`
to the last one's revision), and the cursor at the last one's revision. -/
theorem cmpl_events (V : WEnv GF) (γs : StreamNames) (rr : w64) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (X : w64) (rg : mvcc.WatchRange) (lo : Nat) (c2 : w64)
    (o : OpFull) (hcov : ∀ k, rg.covers k = inRange o.key o.base.rangeEnd k)
    (L2 : mvcc.Log) (d : Nat) (evs : List mvcc.EvM) (kvs : List Loc) (hkl : kvs.length = evs.length)
    (hne : evs ≠ []) (hsnoc : evsOf (Dm ++ [m]) X = evsOf Dm X ++ evs)
    (h2 : evsOf Dm X ++ evs = mvcc.watchEvents L2 rg lo d) (hd : d ≤ L2.length ∨ d ≤ lo)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel)
    (hr : r.events = List.zipWith evModelOf evs kvs) (hv : ¬ watchErr v) :
    cur2Ok V γs rr Dm X rg lo c2 ∗ □ V.W.histLb L2 ∗ srvWLaws V.W ∗
      □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc), ⌜evs[k]? = some ev⌝ → ⌜kvs[k]? = some kv⌝ →
        mvcc.kvPtrFixed kv ev.kv) ⊢
      ∃ c2' : w64, rawRespOk V.W o c2 c2' v r ∗
        cur2Ok V γs rr (Dm ++ [m]) X rg lo c2' := by
  iintro ⟨#Hc, #HL2, #Hl, #Hkv⟩
  unfold cur2Ok
  icases Hc with ⟨⟨%L, %q, #HL, %Hq⟩, -⟩
  obtain ⟨hc2, h1, hlo, hq, hq63⟩ := Hq
  ihave %Hcmp := cLog_cmp V.W L L2 $$ [$Hl $HL $HL2]
  ihave %Hw2 := srvWLaws_model V.W L2 $$ [$Hl $HL2]
  have hlen2 : L2.length < 2 ^ 63 := Hw2.2.1
  obtain ⟨hqd, hd2, hev⟩ := cmpl_events_cut L L2 Hcmp rg lo q d (evsOf Dm X) evs h1 hlo hq h2 hd hne
  obtain ⟨q', hlast, hq1, hq2, htail, hmem⟩ := cmpl_events_last L2 hlen2 rg q d evs hev hne hd2
  have hzq : sint.Z c2 = (q : Int) := by rw [hc2]; word
  have hzq' : sint.Z (W64 (q' : Int)) = (q' : Int) := by word
  have hnq : sint.nat c2 = q := by show (sint.Z c2).toNat = q; rw [hzq]; simp
  have hnq' : sint.nat (W64 (q' : Int)) = q' := by show (sint.Z (W64 (q' : Int))).toNat = q'; rw [hzq']; simp
  -- the events are the log's range events from `q + 1` to `q' + 1`
  have hevs : rangeLogEvents L2 o (sint.nat c2 + 1) (sint.nat (W64 (q' : Int)) + 1) = evs := by
    rw [hnq, hnq', rangeLogEvents_watchEvents L2 o rg hcov, hev,
      mvcc.watchEvents_append L2 rg (show q + 1 ≤ q' + 1 by omega) (show q' + 1 ≤ d by omega),
      htail, List.append_nil]
  iexists W64 (q' : Int)
  have hrevs : r.events.map EvModel.rev = evs.map (fun e => e.kv.modRev) := by
    rw [hr]; exact zipWith_evModel_rev evs kvs hkl
  isplitr
  · unfold rawRespOk
    iright; iright; iright
    isplitr
    · ipureintro
      refine ⟨hv, ?_, by omega, by omega, ?_⟩
      · rw [hr]; intro h
        have := congrArg List.length h
        simp only [List.length_zipWith, List.length_nil] at this
        exact hne (List.eq_nil_of_length_eq_zero (by omega))
      · rw [← List.getLast?_map, hrevs, List.getLast?_map]
        simpa using hlast
    iexists L2, kvs
    iframe HL2
    rw [hevs]
    isplitr
    · ipureintro; exact ⟨by omega, hkl, hr⟩
    iintro !> %k %ev %kv %h1 %h2
    iapply Hkv $$ %k %ev %kv %h1 %h2
  isplitr
  · iexists L2, q'
    isplitr
    · unfold cLog; iright; iexact HL2
    ipureintro
    refine ⟨rfl, ?_, by omega, Or.inl (by omega), by omega⟩
    rw [hsnoc, h2, mvcc.watchEvents_append L2 rg (show lo ≤ q' + 1 by omega) (show q' + 1 ≤ d by omega),
      htail, List.append_nil]
  iright; ileft
  ipureintro
  rw [hsnoc]
  cases hl : evs.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.1 hl) hne
  | some e =>
    refine ⟨e, by rw [List.getLast?_append, hl]; rfl, ?_⟩
    rw [hl] at hlast; simp at hlast; exact hlast.symm

/-- **The second cursor over a progress notification** at `p` (an event-less mvcc response `x`,
the `n`-th the run received, of revision `p`, sent down after `Dm` while the substream's id `X`
was live, at its place in the received list; `q ≤ p` the cursor): the events so far are the watch
events `[lo, dd)` of a certified log `Lc`, `dd` the notification's coverage (`p + 1 ≤ dd`, and
`dd ≤ p + 1` unless no event was delivered, `dd ≤ lo`), and the watch's start is at most `p + 1`.
The server-level contract (a progress notification: past the cursor, `Lc` reaches `p` and has no
range event in `(q, p]`; at the cursor, nothing; at revision `0`, a response without events that
is not one) and the cursor at `p` (or kept). -/
theorem cmpl_prog (V : WEnv GF) (γs : StreamNames) (rr : w64) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (x : mvcc.api.WResp) (pre : List mvcc.api.WResp) (X : w64)
    (rg : mvcc.WatchRange) (lo : Nat)
    (c2 : w64) (o : OpFull) (hcov : ∀ k, rg.covers k = inRange o.key o.base.rangeEnd k)
    (Lc : mvcc.Log) (dd p q : Nat) (hpx : x.rev = W64 (p : Int))
    (hp63 : p < 2 ^ 63) (hqc : c2 = W64 (q : Int)) (hqp : q ≤ p)
    (hE : evsOf Dm X = mvcc.watchEvents Lc rg lo dd) (hd1 : p + 1 ≤ dd)
    (hd2 : dd ≤ p + 1 ∨ dd ≤ lo) (hd3 : dd ≤ Lc.length ∨ dd ≤ lo) (hlop : lo ≤ p + 1)
    (hlo : lo = (sint.Z rr).toNat) (hrev : 1 ≤ sint.Z rr)
    (hsnoc : evsOf (Dm ++ [m]) X = evsOf Dm X) (hmx : m.src = some (pre.length, x))
    (hxe : x.evs = [])
    (hlive : v3rpc.idLive Dm X)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (hv : ¬ watchErr v)
    (hr : r.events = [] ∧ r.created = false ∧ r.canceled = false ∧ r.compactRev = W64 0 ∧
      r.hdrRev = x.rev) :
    cur2Ok V γs rr Dm X rg lo c2 ∗ □ V.W.histLb Lc ∗ srvWLaws V.W ∗ rcvAt γs pre x ⊢
      ∃ c2' : w64, rawRespOk V.W o c2 c2' v r ∗
        cur2Ok V γs rr (Dm ++ [m]) X rg lo c2' := by
  iintro ⟨#Hc, #HLc, #Hl, #Hpos⟩
  obtain ⟨hre, hrc, hrca, hrcomp, hrh⟩ := hr
  have hdd : dd = p + 1 := by omega
  subst hdd
  ihave #Hcm := cur2Ok_mono V γs rr X rg lo c2 hsnoc (List.prefix_append Dm [m]) $$ Hc
  ihave #Hc' := Hc
  iunfold cur2Ok at Hc'
  icases Hc' with ⟨⟨%L, %q', #HL, %Hq⟩, -⟩
  obtain ⟨hc2', h1, hlo1, hq1, hq63⟩ := Hq
  have hqq : q = q' := by
    rw [hqc] at hc2'
    exact W64_inj_of_lt (by omega) (by omega) hc2'
  subst hqq
  have hzq : sint.Z c2 = (q : Int) := by rw [hqc]; word
  have hzp : sint.Z r.hdrRev = (p : Int) := by rw [hrh, hpx]; word
  by_cases hp0 : p = 0
  · -- revision `0`: not a progress notification, the cursor kept
    iexists c2
    iframe Hcm
    unfold rawRespOk
    iright; ileft
    ipureintro
    refine ⟨hv, hre, ?_, rfl⟩
    unfold RespModel.isProgressNotify
    simp [hrh, hpx, hp0]
  have hprog : r.isProgressNotify = true := by
    unfold RespModel.isProgressNotify
    simp only [hre, List.isEmpty_nil, hrca, hrc, hrcomp, hrh, hpx, Bool.not_false, Bool.true_and,
      decide_true, Bool.and_true, Bool.not_eq_true', decide_eq_false_iff_not]
    intro h
    have := W64_inj_of_lt (a := p) (b := 0) (by omega) (by omega) (by simpa using h)
    exact hp0 this
  by_cases hq : q = p
  · -- at the cursor
    subst hq
    have hc2r : c2 = r.hdrRev := by rw [hrh, hpx, hqc]
    iexists c2
    iframe Hcm
    unfold rawRespOk
    iright; iright; ileft
    isplitr
    · ipureintro
      exact ⟨hv, hprog, by omega, by omega, hc2r, by omega⟩
    ileft; ipureintro; rw [hc2r]
  -- `q < p`: no event of the range in `(q, p]`
  have hqp' : q < p := by omega
  have hdL : p + 1 ≤ Lc.length := hd3.resolve_right (by omega)
  ihave %Hcmp := cLog_cmp V.W L Lc $$ [$Hl $HL $HLc]
  have hnone0 := cmpl_prog_none L Lc Hcmp rg lo q p hlo1 hq1 hdL hqp (h1.symm.trans hE)
  ihave %Hwc := srvWLaws_model V.W Lc $$ [$Hl $HLc]
  have hp1 : p + 1 < 2 ^ 63 := by have := Hwc.2.1; omega
  iexists W64 (p : Int)
  isplitr
  · unfold rawRespOk
    iright; iright; ileft
    isplitr
    · ipureintro; exact ⟨hv, hprog, by omega, by omega, by rw [hrh, hpx], by omega⟩
    iright
    iexists Lc
    iframe HLc
    ipureintro
    have hnc : sint.nat c2 = q := by show (sint.Z c2).toNat = q; rw [hzq]; simp
    have hnp : sint.nat r.hdrRev = p := by show (sint.Z r.hdrRev).toNat = p; rw [hzp]; simp
    refine ⟨by omega, ?_⟩
    rw [hnc, hnp, rangeLogEvents_watchEvents Lc o rg hcov]
    exact hnone0
  unfold cur2Ok
  isplitr
  · iexists Lc, p
    isplitr
    · unfold cLog; iright; iexact HLc
    ipureintro
    exact ⟨rfl, hsnoc.trans hE, hlop, Or.inl hdL, by omega⟩
  iright; iright
  unfold progAt
  iexists Dm.length, m, x, pre
  iframe Hpos
  ipureintro
  refine ⟨by simp, hmx, hxe, hpx.symm, ?_⟩
  rw [List.take_left' rfl]; exact hlive

/-- **The second cursor is at most a progress notification's revision** `p` (an event-less mvcc
response `x`, the `n`-th the run `r` received, sent down after `Dm` (`mvccOk`), of `r`'s own id `X`
or `-1`; the events so far within `[lo, p + 1)`; the watch's start at most `p + 1`): the start, a
last event (before `p + 1`), or an earlier progress notification (sent before `x` while `X` was
live, so received before it, `fwdIdx`; its revision at most `p`, `progRev`). -/
theorem cmpl_mono (V : WEnv GF) (γs : StreamNames) (rr : w64) (Dm : List v3rpc.WatchRespM)
    (X : w64) (rg : mvcc.WatchRange) (lo : Nat) (c2 : w64) (r : v3rpc.WRun GF) (j : Nat)
    (m : v3rpc.WatchRespM) (n : Nat) (x : mvcc.api.WResp)
    (Lc : mvcc.Log) (p : Nat) (hsrc : m.src = some (n, x))
    (hfi : v3rpc.fwdIdx Dm n x) (hxid : x.id = W64 (-1) ∨ x.id = X) (hxe : x.evs = [])
    (hxc : x.compactRev = W64 0)
    (hEc : evsOf Dm X = mvcc.watchEvents Lc rg lo (p + 1)) (hlop : lo ≤ p + 1)
    (hlo : lo = (sint.Z rr).toNat) (hrev : 1 ≤ sint.Z rr) (hpx : x.rev = W64 (p : Int))
    (hp63 : p < 2 ^ 63) :
    cur2Ok V γs rr Dm X rg lo c2 ∗ streamAuxIs γs (v3rpc.auxOf r) ∗ v3rpc.mvccOk r j m ⊢
      ⌜∃ q : Nat, c2 = W64 (q : Int) ∧ q ≤ p⌝ := by
  iintro ⟨#Hc, #Hax, Hm⟩
  iunfold cur2Ok at Hc
  icases Hc with ⟨⟨%L, %q, -, %Hq⟩, (%H | %H | #H)⟩
  · ipureintro
    refine ⟨q, Hq.1, ?_⟩
    have h1 := Hq.1; rw [H] at h1
    have : (q : Int) = sint.Z rr - 1 := by
      have h2 : sint.Z (W64 (q : Int)) = q := by have := Hq.2.2.2.2; word
      rw [← h1] at h2; rw [← h2]; word
    omega
  · obtain ⟨e, he, hc⟩ := H
    have hm : e ∈ mvcc.watchEvents Lc rg lo (p + 1) := by rw [← hEc]; exact List.mem_of_getLast? he
    obtain ⟨j, -, hj2, hj⟩ := v3rpc.watchEvents_mem_rev Lc rg lo (p + 1) e hm
    ipureintro
    refine ⟨q, Hq.1, ?_⟩
    have h1 := Hq.1; rw [hc, hj] at h1
    have := W64_inj_of_lt (by omega) (by have := Hq.2.2.2.2; omega) h1
    omega
  · iunfold progAt at H
    icases H with ⟨%i, %my, %y, %prey, %Hy, #Hpos⟩
    obtain ⟨hi, hs, hye, hc, hl⟩ := Hy
    have hyx : prey.length < n := by
      refine hfi i my prey.length y hi hs ?_
      rcases hxid with h | h
      · left; exact h
      · right; rw [h]; exact hl
    iunfold rcvAt at Hpos
    icases Hpos with ⟨%r', #Hax', #Hlb'⟩
    ihave %He : iprop(⌜v3rpc.auxOf r = v3rpc.auxOf r'⌝) $$ []
    · iapply streamAuxIs_agree
      isplit
      · iexact Hax
      · iexact Hax'
    obtain ⟨-, -, hγr, -⟩ := v3rpc.auxOf_inj He
    ihave #Hlb : v3rpc.rcvLb r.γr (prey ++ [y]) $$ []
    · rw [hγr]; iexact Hlb'
    ihave %hle := progRev r j m n x prey y hsrc hyx hye hxe hxc $$ [Hm Hlb]
    · iframe Hm Hlb
    ipureintro
    refine ⟨q, Hq.1, ?_⟩
    rw [← hc, Hq.1, hpx] at hle
    have h3 := Hq.2.2.2.2
    have e1 : sint.Z (W64 (q : Int)) = q := by word
    have e2 : sint.Z (W64 (p : Int)) = p := by word
    omega

/-- The events received up to an event-less response are those received before it. -/
theorem recvEvs_snoc_nil (pre : List mvcc.api.WResp) (x : mvcc.api.WResp) (X : w64)
    (hxe : x.evs = []) : mvcc.api.recvEvs (pre ++ [x]) X = mvcc.api.recvEvs pre X := by
  unfold mvcc.api.recvEvs
  rw [List.filter_append, List.map_append, List.flatten_append]
  by_cases h : x.id = X <;> simp [h, hxe]

/-- **The events so far, by a progress notification's coverage** (`progressCov`'s, for the
watch id `X` whose received events up to `x` are the watch events `[lo, rev + 1)` of a certified
log `Lc`, `x` within it; the forwarding fact `fwdEvs` for its live id): the watch events
`[lo, dd)` of `Lc`, `dd` the notification's coverage (`p + 1`), its revision `p ≥ lo - 1`. -/
theorem cmpl_cov (Dm : List v3rpc.WatchRespM) (x : mvcc.api.WResp) (pre : List mvcc.api.WResp)
    (X : w64) (rg : mvcc.WatchRange) (lo : Nat) (Lc : mvcc.Log)
    (hfe : v3rpc.sentEvsOf Dm X =
      (pre.filter (fun y => decide (y.id = X))).filter (fun y => decide (y.evs ≠ [])))
    (hxe : x.evs = [])
    (hrec : mvcc.api.recvEvs (pre ++ [x]) X = mvcc.watchEvents Lc rg lo (sint.nat x.rev + 1))
    (hlor : (lo : Int) ≤ sint.Z x.rev + 1) (hlen : sint.nat x.rev < Lc.length)
    (hlo1 : 1 ≤ lo) :
    ∃ (dd p : Nat), x.rev = W64 (p : Int) ∧ p < 2 ^ 63 ∧
      evsOf Dm X = mvcc.watchEvents Lc rg lo dd ∧
      p + 1 ≤ dd ∧ (dd ≤ p + 1 ∨ dd ≤ lo) ∧ (dd ≤ Lc.length ∨ dd ≤ lo) ∧ lo ≤ p + 1 := by
  have hx0 : 0 ≤ sint.Z x.rev := by omega
  have hx63 : sint.Z x.rev < 2 ^ 63 := by word
  have hp : sint.nat x.rev = (sint.Z x.rev).toNat := rfl
  refine ⟨sint.nat x.rev + 1, sint.nat x.rev, by rw [hp]; word, by omega, ?_, by omega,
    Or.inl (Nat.le_refl _), Or.inl (by omega), by omega⟩
  rw [← hrec, recvEvs_snoc_nil pre x X hxe]
  unfold evsOf mvcc.api.recvEvs
  rw [hfe, flatten_evs_filter]

end chain
end client
end EtcdGrove
end Perennial
