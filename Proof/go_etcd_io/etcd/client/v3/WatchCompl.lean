/-
**A watch's completeness, as the cache's contract states it** (the watch slice's unit W-K, K2e-7):
from mvcc's watch events of a sealed log to the cache's chain of steps (`watchChain`,
`cache/v3/InvEtcd.lean`), for a watch whose range covers exactly the keys under a prefix. Lean-first,
no Rocq counterpart.

* `splitBatches_head`, `splitBatches_block`: a leading block of one revision's events, followed by
  later ones, is the first batch.
* `watchChain_of_watch`: the watch events of the revisions `[b, d)` of a sealed small log, with no
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
      rw [ht]; exact concurrency.goStringLt_nil_cons a t
    simp [hlt]
  · simp [hk0, hkey, h0]

/-! ## The second cursor's steps (pure) -/

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

open Iris Iris.BI Iris.ProofMode

/-- **One revision's watch events, as one batch's step** (`etcdStepCertBody`): from `p` to `b`,
no watch event in `[p + 1, b)`, the events of `b` (with their key-values read-only at `kvs`). -/
theorem stepCert_of_watch (V : WEnv GF) (L : mvcc.Log) (rg : mvcc.WatchRange) (pfx : GoString)
    (hcov : ∀ k, rg.covers k = true ↔ pfx <+: k) (p b : Nat) (hpb : p + 1 ≤ b) (hb : b < L.length)
    (hst : V.R.γ.st = V.R.E.γ) (hnone : mvcc.watchEvents L rg (p + 1) b = []) (kvs : List Loc)
    (hkl : kvs.length = (mvcc.watchEvents L rg b (b + 1)).length)
    (hAne : mvcc.watchEvents L rg b (b + 1) ≠ []) :
    mvcc.evLog V.R.γ.st L ∗ srvLogsSmall V.R ∗
      □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc), ⌜(mvcc.watchEvents L rg b (b + 1))[k]? = some ev⌝ →
        ⌜kvs[k]? = some kv⌝ → mvcc.kvPtrFixed kv ev.kv) ⊢
      etcdStepCertBody (EM := V.EM) pfx (W64 (p : Int))
        (List.zipWith evModelOf (mvcc.watchEvents L rg b (b + 1)) kvs) := by
  iintro ⟨#HL, #Hsm, #Hkv⟩
  ihave #Hs := mvcc.evLog_sealed _ _ $$ HL
  ihave #Hc := mvcc.evLog_certOk _ _ $$ HL
  irevert Hs Hc; rw [hst]; iintro #Hs #Hc
  ihave %Hsmall : ⌜LogSmall L⌝ $$ []
  · iunfold srvLogsSmall at Hsm
    iapply Hsm; rw [hst]; iexact Hs
  ihave #Hsl : v3rpc.srvLog V.R.E L $$ []
  · unfold v3rpc.srvLog; iframe Hs; ipureintro; exact Hsmall
  ihave %Hw := v3rpc.sealed_pure _ L $$ Hs
  have hlen : L.length < 2 ^ 63 := Hw.2
  have hnone' : ∀ x : Nat, p < x → x < b → mvcc.watchEvents L rg x (x + 1) = [] := by
    intro x h1 h2
    have := hnone
    rw [mvcc.watchEvents_append L rg (show p + 1 ≤ x by omega) (show x ≤ b by omega),
      mvcc.watchEvents_append L rg (show x ≤ x + 1 by omega) (show x + 1 ≤ b by omega)] at this
    exact (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 this).2).1
  ihave #Hstep := v3rpc.srvStep_of_watch V.R.E L rg pfx hcov p b (by omega) hb hnone' $$ [Hsl Hc]
  · iframe #
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
  iapply v3rpc.etcdReached_of_certOk V.R.E L (W64 (b : Int)) (by word) $$ Hc

/-- **A block of watch events as the cache's chain of steps** (`watchChain`): the watch events of
`[b, d)` of a sealed log (`d` within it), a range covering exactly the keys under `pfx`, no watch
event in `[p + 1, b)`: a chain of steps from `p`, one per revision with events. -/
theorem watchChain_of_watch (V : WEnv GF) (L : mvcc.Log) (rg : mvcc.WatchRange) (pfx : GoString)
    (hcov : ∀ k, rg.covers k = true ↔ pfx <+: k) (d : Nat) (hd : d ≤ L.length)
    (hst : V.R.γ.st = V.R.E.γ) :
    ∀ (n p b : Nat) (kvs : List Loc), d - b = n → p + 1 ≤ b →
      mvcc.watchEvents L rg (p + 1) b = [] →
      kvs.length = (mvcc.watchEvents L rg b d).length →
      mvcc.evLog V.R.γ.st L ∗ srvLogsSmall V.R ∗
        □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc), ⌜(mvcc.watchEvents L rg b d)[k]? = some ev⌝ →
          ⌜kvs[k]? = some kv⌝ → mvcc.kvPtrFixed kv ev.kv) ⊢
      watchChain (EM := V.EM) pfx (W64 (p : Int))
        (splitBatches (List.zipWith evModelOf (mvcc.watchEvents L rg b d) kvs))
  | 0, p, b, kvs, hn, _, _, _ => by
    rw [mvcc.watchEvents_empty L rg (show d ≤ b by omega)]
    iintro -
    simp only [List.zipWith_nil_left, splitBatches]
    unfold watchChain; itrivial
  | n + 1, p, b, kvs, hn, hpb, hnone, hkl => by
    iintro ⟨#HL, #Hsm, #Hkv⟩
    ihave #Hs := mvcc.evLog_sealed _ _ $$ HL
    ihave %Hw := v3rpc.sealed_pure _ L $$ Hs
    have hlen : L.length < 2 ^ 63 := Hw.2
    have hsplit := mvcc.watchEvents_append L rg (show b ≤ b + 1 by omega) (show b + 1 ≤ d by omega)
    by_cases hA : mvcc.watchEvents L rg b (b + 1) = []
    · -- no event at `b`: on to `b + 1`, from the same `p`
      have hevs : mvcc.watchEvents L rg b d = mvcc.watchEvents L rg (b + 1) d := by
        rw [hsplit, hA, List.nil_append]
      rw [hevs] at hkl ⊢
      iapply watchChain_of_watch V L rg pfx hcov d hd hst n p (b + 1) kvs (by omega) (by omega)
        (by rw [mvcc.watchEvents_append L rg hpb (show b ≤ b + 1 by omega), hnone, hA]; rfl) hkl
      iframe HL Hsm
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
      · have H1 := stepCert_of_watch V L rg pfx hcov p b hpb (by omega) hst hnone (kvs.take A.length)
          (by rw [hAe]; simp [hkl']) (by rw [hAe]; exact hA)
        rw [hAe] at H1
        iapply H1
        iframe HL Hsm
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
      have H2 := watchChain_of_watch V L rg pfx hcov d hd hst n b (b + 1) (kvs.drop A.length)
        (by omega) (by omega) (mvcc.watchEvents_empty L rg (Nat.le_refl _)) (by rw [hBe]; simp [hkl'])
      rw [hBe] at H2
      iapply H2
      iframe HL Hsm
      iintro !> %k %ev %kv %h1 %h2
      rw [List.getElem?_drop] at h2
      iapply Hkv $$ %(A.length + k) %ev %kv
        %(by rw [List.getElem?_append_right (by omega)]; simpa using h1) %h2

/-! ## The second cursor -/

/-- **A response's place on its stream's channel** (persistent): the channel's sent list (named
by the stream's auxiliary name) had the responses `pre`, then `y`, at `y`'s index. -/
def chanPos (γs : StreamNames) (y : mvcc.RespM) : IProp GF :=
  iprop(∃ (γc : mvcc.WatchChanNames) (pre : List mvcc.RespM) (γo : mvcc.WsStreamNames) (γa : GName),
    streamAuxIs γs (v3rpc.auxOf γo γa) ∗ ⌜γo.sentl = γc.sentl ∧ y.idx = pre.length⌝ ∗
    mvcc.chanSentLb γc (pre ++ [y]))

instance chanPos_persistent (γs : StreamNames) (y : mvcc.RespM) :
    Persistent (chanPos (GF := GF) γs y) := by
  unfold chanPos; infer_instance

/-- **The second cursor at a progress notification's revision** (persistent): `c2` is the
revision of an event-less mvcc response `y`, the `i`th of the responses `Dm` received, sent while
the id `X` was live, at its place on the channel. -/
def progAt (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (X c2 : w64) : IProp GF :=
  iprop(∃ (i : Nat) (my : v3rpc.WatchRespM) (y : mvcc.RespM),
    ⌜Dm[i]? = some my ∧ my.src = some y ∧ y.evs = [] ∧ c2 = y.rev ∧ v3rpc.idLive (Dm.take i) X⌝ ∗
    chanPos γs y)

instance progAt_persistent (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (X c2 : w64) :
    Persistent (progAt (GF := GF) γs Dm X c2) := by
  unfold progAt; infer_instance

theorem progAt_mono (γs : StreamNames) {Dm Dm' : List v3rpc.WatchRespM} (X c2 : w64)
    (hp : Dm <+: Dm') : progAt (GF := GF) γs Dm X c2 ⊢ progAt γs Dm' X c2 := by
  unfold progAt
  iintro ⟨%i, %my, %y, %H, #Hp⟩
  obtain ⟨t, rfl⟩ := hp
  have hi : i < Dm.length := (List.getElem?_eq_some_iff.1 H.1).1
  iexists i, my, y
  iframe Hp
  ipureintro
  rw [List.getElem?_append_left hi, List.take_append_of_le_length (Nat.le_of_lt hi)]
  exact H

/-- **The second dispatch cursor `c2` of a registered substream** (persistent; its watcher `w`,
range `rg`, first revision `lo`, id `X`, the responses `Dm` received): the events so far are the
watch events `[lo, q + 1)` of a watched log (`c2 = q`; `q + 1` within it, or `lo`), and `c2` is
the watch's start, the last event's revision, or a progress notification's (`progAt`). -/
def cur2Ok (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (Dm : List v3rpc.WatchRespM) (X : w64)
    (w : Loc) (rg : mvcc.WatchRange) (lo : Nat) (c2 : w64) : IProp GF :=
  iprop((∃ (L : mvcc.Log) (q : Nat), mvcc.evLog V.R.γ.st L ∗
      ⌜c2 = W64 (q : Int) ∧ evsOf Dm w = mvcc.watchEvents L rg lo (q + 1) ∧ lo ≤ q + 1 ∧
        (q + 1 ≤ L.length ∨ q + 1 = lo) ∧ q + 1 < 2 ^ 63⌝) ∗
    (⌜c2 = P.rev - W64 1⌝ ∨ ⌜∃ e, (evsOf Dm w).getLast? = some e ∧ c2 = e.kv.modRev⌝ ∨
      progAt γs Dm X c2))

instance cur2Ok_persistent (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF)
    (Dm : List v3rpc.WatchRespM) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (lo : Nat) (c2 : w64) :
    Persistent (cur2Ok V γs P Dm X w rg lo c2) := by
  unfold cur2Ok; infer_instance

/-- `cur2Ok` over more responses, none of the watcher's events. -/
theorem cur2Ok_mono (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) {Dm Dm' : List v3rpc.WatchRespM}
    (X : w64) (w : Loc) (rg : mvcc.WatchRange) (lo : Nat) (c2 : w64) (h : evsOf Dm' w = evsOf Dm w)
    (hp : Dm <+: Dm') :
    cur2Ok (GF := GF) V γs P Dm X w rg lo c2 ⊢ cur2Ok V γs P Dm' X w rg lo c2 := by
  unfold cur2Ok
  rw [h]
  iintro ⟨#H1, (#H2 | #H2 | #H2)⟩
  · iframe H1; ileft; iexact H2
  · iframe H1; iright; ileft; iexact H2
  · iframe H1; iright; iright; iapply progAt_mono γs X c2 hp $$ H2

/-- **The second cursor at the watch's start** `rev - 1` (`rev ≥ 1`, the first revision `lo`
the start revision), no events yet. -/
theorem cur2Ok_init (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (Dm : List v3rpc.WatchRespM)
    (X : w64) (w : Loc) (rg : mvcc.WatchRange) (lo : Nat) (hrev : 1 ≤ sint.Z P.rev)
    (hlo : lo = (sint.Z P.rev).toNat) (hE : evsOf Dm w = []) :
    ⊢ |==> cur2Ok (GF := GF) V γs P Dm X w rg lo (P.rev - W64 1) := by
  imod mvcc.evLog_nil V.R.γ.st with #Hn
  imodintro
  unfold cur2Ok
  isplitr
  · iexists [], (sint.Z P.rev).toNat - 1
    iframe Hn
    ipureintro
    have h1 : ((sint.Z P.rev).toNat - 1 : Nat) + 1 = (sint.Z P.rev).toNat := by omega
    refine ⟨by word, ?_, by omega, Or.inr (by omega), by word⟩
    rw [hE, h1, ← hlo, mvcc.watchEvents_empty _ _ (Nat.le_refl _)]
  ileft; ipureintro; rfl

/-- **The second cursor over a response with events** `evs` (the watcher's: the events so far
then `evs` are the watch events `[lo, d)` of a watched log `L2`; their key-values read-only at
`kvs`): the cache's contract from `c2` (events, `watchChain`), and the cursor at the last one's
revision. -/
theorem cmpl_events (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (lo : Nat) (c2 : w64)
    (pfx : GoString) (hcov : ∀ k, rg.covers k = true ↔ pfx <+: k) (hst : V.R.γ.st = V.R.E.γ)
    (L2 : mvcc.Log) (d : Nat) (evs : List mvcc.EvM) (kvs : List Loc) (hkl : kvs.length = evs.length)
    (hne : evs ≠ []) (hsnoc : evsOf (Dm ++ [m]) w = evsOf Dm w ++ evs)
    (h2 : evsOf Dm w ++ evs = mvcc.watchEvents L2 rg lo d) (hd : d ≤ L2.length ∨ d ≤ lo)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel)
    (hr : r.events = List.zipWith evModelOf evs kvs) (hv : ¬ watchErr v) :
    cur2Ok V γs P Dm X w rg lo c2 ∗ mvcc.evLog V.R.γ.st L2 ∗ srvLogsSmall V.R ∗
      □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc), ⌜evs[k]? = some ev⌝ → ⌜kvs[k]? = some kv⌝ →
        mvcc.kvPtrFixed kv ev.kv) ⊢
      ∃ c2' : w64, watchRespOk (EM := V.EM) pfx c2 c2' v r ∗
        cur2Ok V γs P (Dm ++ [m]) X w rg lo c2' := by
  iintro ⟨#Hc, #HL2, #Hsm, #Hkv⟩
  unfold cur2Ok
  icases Hc with ⟨⟨%L, %q, #HL, %Hq⟩, -⟩
  obtain ⟨hc2, h1, hlo, hq, hq63⟩ := Hq
  ihave %Hcmp := mvcc.evLog_cmp V.R.γ.st L L2 $$ HL HL2
  ihave #Hs2 := mvcc.evLog_sealed _ _ $$ HL2
  ihave %Hw2 := v3rpc.sealed_pure _ L2 $$ Hs2
  have hlen2 : L2.length < 2 ^ 63 := Hw2.2
  obtain ⟨hqd, hd2, hev⟩ := cmpl_events_cut L L2 Hcmp rg lo q d (evsOf Dm w) evs h1 hlo hq h2 hd hne
  obtain ⟨q', hlast, hq1, hq2, htail, hmem⟩ := cmpl_events_last L2 hlen2 rg q d evs hev hne hd2
  iexists W64 (q' : Int)
  have hrevs : r.events.map EvModel.rev = evs.map (fun e => e.kv.modRev) := by
    rw [hr]; exact zipWith_evModel_rev evs kvs hkl
  isplitr
  · unfold watchRespOk
    iright; iright; iright
    isplitr
    · ipureintro
      refine ⟨hv, ?_, ?_, ?_, ?_⟩
      · rw [hr]; intro h
        have := congrArg List.length h
        simp only [List.length_zipWith, List.length_nil] at this
        exact hne (List.eq_nil_of_length_eq_zero (by omega))
      · unfold EvRevSorted
        have hp : (r.events.map EvModel.rev).Pairwise (fun x y => sint.Z x ≤ sint.Z y) := by
          rw [hrevs, List.pairwise_map, hev]; exact watchEvents_sorted L2 hlen2 rg (q + 1) d
        exact (List.pairwise_map (f := EvModel.rev) (R := fun x y => sint.Z x ≤ sint.Z y)).1 hp
      · intro e he
        rw [hr] at he
        obtain ⟨ev, hev', hre⟩ := mem_zipWith_evModel he
        obtain ⟨j, hj1, hj2, hj⟩ := hmem ev hev'
        rw [hre, hj, hc2]
        constructor <;> word
      · rw [← List.getLast?_map, hrevs, List.getLast?_map]
        simpa using hlast
    rw [hc2, hr]
    have hkl' : kvs.length = (mvcc.watchEvents L2 rg (q + 1) d).length := by rw [← hev]; exact hkl
    have H := watchChain_of_watch V L2 rg pfx hcov d hd2 hst (d - (q + 1)) q (q + 1) kvs rfl
      (Nat.le_refl _) (mvcc.watchEvents_empty L2 rg (Nat.le_refl _)) hkl'
    rw [← hev] at H
    iapply H
    iframe HL2 Hsm
    iintro !> %k %ev %kv %h1 %h2
    iapply Hkv $$ %k %ev %kv %h1 %h2
  isplitr
  · iexists L2, q'
    iframe HL2
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

/-- **The second cursor over a progress notification** at `p` (an event-less mvcc response `x`
of revision `p`, sent down after `Dm` while the substream's id `X` was live, at its place on the
channel; `q ≤ p` the cursor): the events so far are the watch events `[lo, dd)` of a watched log
`Lc`, `dd` the notification's coverage (`p + 1 ≤ dd`, and `dd ≤ p + 1` unless no event was
delivered, `dd ≤ lo`), and the watch's start is at most `p + 1`. The cache's contract (a progress
notification, or, at revision `0`, a response without events that is not one) and the cursor at
`p`. -/
theorem cmpl_prog (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (x : mvcc.RespM) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (lo : Nat)
    (c2 : w64) (pfx : GoString) (hcov : ∀ k, rg.covers k = true ↔ pfx <+: k)
    (hst : V.R.γ.st = V.R.E.γ) (Lc : mvcc.Log) (dd p q : Nat) (hpx : x.rev = W64 (p : Int))
    (hp63 : p < 2 ^ 63) (hqc : c2 = W64 (q : Int)) (hqp : q ≤ p)
    (hE : evsOf Dm w = mvcc.watchEvents Lc rg lo dd) (hd1 : p + 1 ≤ dd)
    (hd2 : dd ≤ p + 1 ∨ dd ≤ lo) (hd3 : dd ≤ Lc.length ∨ dd ≤ lo) (hlop : lo ≤ p + 1)
    (hlo : lo = (sint.Z P.rev).toNat) (hrev : 1 ≤ sint.Z P.rev)
    (hsnoc : evsOf (Dm ++ [m]) w = evsOf Dm w) (hmx : m.src = some x) (hxe : x.evs = [])
    (hlive : v3rpc.idLive Dm X)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (hv : ¬ watchErr v)
    (hr : r.events = [] ∧ r.created = false ∧ r.canceled = false ∧ r.compactRev = W64 0 ∧
      r.hdrRev = x.rev) :
    cur2Ok V γs P Dm X w rg lo c2 ∗ mvcc.evLog V.R.γ.st Lc ∗ srvLogsSmall V.R ∗
      etcdReached (EM := V.EM) (P.rev - W64 1) ∗ chanPos γs x ⊢
      ∃ c2' : w64, watchRespOk (EM := V.EM) pfx c2 c2' v r ∗
        cur2Ok V γs P (Dm ++ [m]) X w rg lo c2' := by
  iintro ⟨#Hc, #HLc, #Hsm, #Hr0, #Hpos⟩
  obtain ⟨hre, hrc, hrca, hrcomp, hrh⟩ := hr
  have hdd : dd = p + 1 := by omega
  subst hdd
  ihave #Hcm := cur2Ok_mono V γs P X w rg lo c2 hsnoc (List.prefix_append Dm [m]) $$ Hc
  ihave #Hc' := Hc
  iunfold cur2Ok at Hc'
  icases Hc' with ⟨⟨%L, %q', #HL, %Hq⟩, -⟩
  obtain ⟨hc2', h1, hlo1, hq1, hq63⟩ := Hq
  have hqq : q = q' := by
    rw [hqc] at hc2'
    exact W64_inj_of_lt (by omega) (by omega) hc2'
  subst hqq
  by_cases hp0 : p = 0
  · -- revision `0`: not a progress notification, the cursor kept
    iexists c2
    iframe Hcm
    unfold watchRespOk
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
  -- etcd reached `p`
  ihave #Hreach : etcdReached (EM := V.EM) (W64 (p : Int)) $$ []
  · rcases hd3 with h | h
    · ihave #Hok := mvcc.evLog_certOk _ _ $$ HLc
      irevert Hok; rw [hst]; iintro #Hok
      iapply v3rpc.etcdReached_of_certOk V.R.E Lc (W64 (p : Int)) (by word) $$ Hok
    · have : W64 (p : Int) = P.rev - W64 1 := by
        have : (p : Int) = sint.Z P.rev - 1 := by omega
        word
      rw [this]; iexact Hr0
  by_cases hq : q = p
  · subst hq
    iexists c2
    iframe Hcm
    unfold watchRespOk
    iright; iright; ileft
    isplitr
    · ipureintro
      refine ⟨hv, hprog, ?_, ?_, ?_⟩
      · rw [hrh, hpx, hqc]; exact Int.le_refl _
      · rw [hrh, hpx, hqc]
      · rw [hrh, hpx]; word
    isplitr
    · ileft; ipureintro; rw [hrh, hpx, hqc]
    rw [hrh, hpx]; iexact Hreach
  -- `q < p`: no event of the range in `(q, p]`
  have hqp' : q < p := by omega
  have hdL : p + 1 ≤ Lc.length := hd3.resolve_right (by omega)
  ihave %Hcmp := mvcc.evLog_cmp V.R.γ.st L Lc $$ HL HLc
  have hnone0 := cmpl_prog_none L Lc Hcmp rg lo q p hlo1 hq1 hdL hqp (h1.symm.trans hE)
  ihave #Hs := mvcc.evLog_sealed _ _ $$ HLc
  ihave %Hwc := v3rpc.sealed_pure _ Lc $$ Hs
  have hp1 : p + 1 < 2 ^ 63 := by have := Hwc.2; omega
  ihave %Hsmall : ⌜txn.LogSmall Lc⌝ $$ []
  · iunfold srvLogsSmall at Hsm
    iapply Hsm; iexact Hs
  ihave #Hsl : v3rpc.srvLog V.R.E Lc $$ []
  · unfold v3rpc.srvLog; rw [← hst]; iframe Hs; ipureintro; exact Hsmall
  ihave #HcLc : mvcc.certOk V.R.E.γ Lc $$ []
  · rw [← hst]; iapply mvcc.evLog_certOk; iexact HLc
  have hpe : mvcc.watchEvents Lc rg p (p + 1) = [] :=
    watchEvents_sub_nil Lc rg hnone0 (by omega) (Nat.le_succ p) (Nat.le_refl _)
  have HS := v3rpc.srvStep_of_watch V.R.E Lc rg pfx hcov q p (by omega) (by omega)
    (fun y h1 h2 => watchEvents_sub_nil Lc rg hnone0 (by omega) (Nat.le_succ y) (by omega))
  rw [hpe, List.map_nil] at HS
  ihave #Hstep := HS $$ [Hsl HcLc]
  · iframe #
  iexists W64 (p : Int)
  isplitr
  · unfold watchRespOk
    iright; iright; ileft
    isplitr
    · ipureintro
      refine ⟨hv, hprog, ?_, ?_, ?_⟩
      · rw [hrh, hpx, hqc]; word
      · rw [hrh, hpx]
      · rw [hrh, hpx]; word
    isplitr
    · iright; rw [hrh, hpx, hqc]; iexact Hstep
    rw [hrh, hpx]; iexact Hreach
  unfold cur2Ok
  isplitr
  · iexists Lc, p
    iframe HLc
    ipureintro
    exact ⟨rfl, hsnoc.trans hE, hlop, Or.inl hdL, by omega⟩
  iright; iright
  unfold progAt
  iexists Dm.length, m, x
  iframe Hpos
  ipureintro
  refine ⟨by simp, hmx, hxe, hpx.symm, ?_⟩
  rw [List.take_left' rfl]; exact hlive

/-- Two snapshots of a channel's sent list, the first's last before the second's: the first's
last response is among the second's earlier ones. -/
theorem lb_snoc_mem {pre pre' : List mvcc.RespM} {x y : mvcc.RespM}
    (h : pre' ++ [y] <+: pre ++ [x] ∨ pre ++ [x] <+: pre' ++ [y]) (hlt : pre'.length < pre.length) :
    y ∈ pre := by
  rcases h with h | h
  · obtain ⟨t, ht⟩ := h
    have : (pre ++ [x])[pre'.length]? = some y := by
      rw [← ht, List.getElem?_append_left (by simp), List.getElem?_append_right (Nat.le_refl _)]
      simp
    rw [List.getElem?_append_left hlt] at this
    exact List.mem_of_getElem? this
  · have := h.length_le; simp at this; omega

/-- **The second cursor is at most a progress notification's revision** `p` (an event-less mvcc
response `x` sent down after `Dm`, of `r`'s own id `X` or `-1`, at its place on the channel,
`pre` before it; the events so far within `[lo, p + 1)`; the watch's start at most `p + 1`): the
start, a last event (before `p + 1`), or an earlier progress notification (sent before `x` while
`X` was live, so on the channel before it: `respRev`). -/
theorem cmpl_mono (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (Dm : List v3rpc.WatchRespM)
    (X : w64) (w : Loc) (rg : mvcc.WatchRange) (lo : Nat) (c2 : w64) (x : mvcc.RespM)
    (γc : mvcc.WatchChanNames) (pre : List mvcc.RespM) (γo : mvcc.WsStreamNames) (γa : GName)
    (Lc : mvcc.Log) (p : Nat) (hγ : γo.sentl = γc.sentl) (hidx : x.idx = pre.length)
    (hfi : v3rpc.fwdIdx Dm x) (hxid : x.id = W64 (-1) ∨ x.id = X) (hxe : x.evs = [])
    (hEc : evsOf Dm w = mvcc.watchEvents Lc rg lo (p + 1)) (hlop : lo ≤ p + 1)
    (hlo : lo = (sint.Z P.rev).toNat) (hrev : 1 ≤ sint.Z P.rev) (hpx : x.rev = W64 (p : Int))
    (hp63 : p < 2 ^ 63) :
    cur2Ok V γs P Dm X w rg lo c2 ∗ streamAuxIs γs (v3rpc.auxOf γo γa) ∗
      mvcc.chanSentLb γc (pre ++ [x]) ∗ mvcc.respRev V.R.γ pre x ⊢
      ⌜∃ q : Nat, c2 = W64 (q : Int) ∧ q ≤ p⌝ := by
  iintro ⟨#Hc, #Hax, #Hlb, #Hrr⟩
  iunfold cur2Ok at Hc
  icases Hc with ⟨⟨%L, %q, -, %Hq⟩, (%H | %H | #H)⟩
  · ipureintro
    refine ⟨q, Hq.1, ?_⟩
    have h1 := Hq.1; rw [H] at h1
    have : (q : Int) = sint.Z P.rev - 1 := by
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
    icases H with ⟨%i, %my, %y, %Hy, #Hpos⟩
    obtain ⟨hi, hs, hye, hc, hl⟩ := Hy
    have hyx : y.idx < x.idx := by
      refine hfi i my y hi hs ?_
      rcases hxid with h | h
      · left; exact h
      · right; rw [h]; exact hl
    iunfold chanPos at Hpos
    icases Hpos with ⟨%γc', %pre', %γo', %γa', #Hax', %Hγ', #Hlb'⟩
    ihave %He : iprop(⌜v3rpc.auxOf γo γa = v3rpc.auxOf γo' γa'⌝) $$ []
    · iapply streamAuxIs_agree
      isplit
      · iexact Hax
      · iexact Hax'
    obtain ⟨rfl, -⟩ := v3rpc.auxOf_inj He
    iunfold mvcc.chanSentLb at Hlb Hlb'
    irevert Hlb'; rw [← Hγ'.1, hγ]; iintro #Hlb'
    ihave %Hcmp := mono_list_lb_valid γc.sentl (pre' ++ [y]) (pre ++ [x]) $$ Hlb' Hlb
    have hy : y ∈ pre := lb_snoc_mem Hcmp (by omega)
    iunfold mvcc.respRev at Hrr
    icases Hrr with (%hne | ⟨%Ln, -, %Hn⟩)
    · exact absurd hxe hne
    have hle := Hn.2 y hy hye
    ipureintro
    refine ⟨q, Hq.1, ?_⟩
    rw [← hc, Hq.1, hpx] at hle
    have h3 := Hq.2.2.2.2
    have e1 : sint.Z (W64 (q : Int)) = q := by word
    have e2 : sint.Z (W64 (p : Int)) = p := by word
    omega

/-- **The events so far, by a progress notification's coverage** (`covFact` of the watcher `w`,
a start-read watch of the range `rg` from `lo`, no filters; the forwarding fact `fwdEvs` for its
live id): the watch events `[lo, dd)` of a watched log `Lc`, `dd` the notification's coverage
(`p + 1 ≤ dd ≤ p + 1` unless no event was delivered), its revision `p ≥ lo - 1`. -/
theorem cmpl_cov (V : WEnv GF) (Dm : List v3rpc.WatchRespM) (x : mvcc.RespM)
    (γc : mvcc.WatchChanNames) (pre : List mvcc.RespM) (w : Loc) (rg : mvcc.WatchRange)
    (fcs : GoSlice) (lo : Nat) (hfe : v3rpc.sentEvsOf Dm w =
      (pre.filter (fun y => decide (y.w = w))).filter (fun y => decide (y.evs ≠ [])))
    (hlo1 : 1 ≤ lo) :
    mvcc.covFact (GF := GF) V.R.γ γc pre w x.rev ∗ mvcc.watcherIs V.R.γ w rg fcs lo ∗
      fcs ↦*□ ([] : List GoFunc) ∗
      (∃ γw : mvcc.WatcherNames, mvcc.watcherMeta V.R.γ w γw ∗ ⌜γw.sr = true⌝) ⊢
      ∃ (Lc : mvcc.Log) (dd p : Nat), mvcc.evLog (GF := GF) V.R.γ.st Lc ∗
        ⌜x.rev = W64 (p : Int) ∧ p < 2 ^ 63 ∧ evsOf Dm w = mvcc.watchEvents Lc rg lo dd ∧
          p + 1 ≤ dd ∧ (dd ≤ p + 1 ∨ dd ≤ lo) ∧ (dd ≤ Lc.length ∨ dd ≤ lo) ∧ lo ≤ p + 1⌝ := by
  iintro ⟨#Hcf, #Hw, #Hfcs, ⟨%γw1, #Hm1, %Hsr⟩⟩
  iunfold mvcc.covFact at Hcf
  icases Hcf with ⟨%γw, %r, %fcs', %D, %L, %d, #Hm, -, #Hf, #HL, #HDf, %HD⟩
  iunfold mvcc.watcherIs at Hw
  icases Hw with ⟨%γw0, %C, #Hm0, #Hf0, -, -, %Hlo⟩
  ihave %Hag : iprop(⌜rg = r ∧ fcs = fcs'⌝) $$ []
  · iapply mvcc.watcherFixed_agree
    isplit
    · iexact Hf0
    · iexact Hf
  obtain ⟨rfl, rfl⟩ := Hag
  iunfold mvcc.watcherMeta at Hm Hm0 Hm1
  ihave %Hmeq := ghostMapElem_agree _ _ _ _ _ _ $$ Hm Hm0
  ihave %Hmeq1 := ghostMapElem_agree _ _ _ _ _ _ $$ Hm Hm1
  subst Hmeq Hmeq1
  ihave %Hkeep : ⌜∀ dl ∈ D, dl.2 = dl.1⌝ $$ []
  · iintro %dl %hdl
    icases HDf $$ %dl %hdl with ⟨%fs, Hfi, %Hdl⟩
    iunfold mvcc.filtersImpl at Hfi
    icases Hfi with ⟨%fps, #Hfps, %Hlen, -⟩
    ihave %Heq := ownSlice_agree _ _ _ _ _ $$ Hfps Hfcs
    subst Heq
    have hfs : fs = [] := List.eq_nil_of_length_eq_zero (by simpa using Hlen.symm)
    subst hfs
    ipureintro
    rw [Hdl]
    unfold mvcc.filtered
    simp
  obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := HD
  have hlo' : (γw.lo : Int) ≤ sint.Z x.rev + 1 := h7 Hsr
  rw [Hlo.1] at h2 h3 h5 hlo'
  have hx0 : 0 ≤ sint.Z x.rev := by omega
  iexists L, d, (sint.Z x.rev).toNat
  iframe HL
  ipureintro
  have hall : D.filter mvcc.Deliv.sent = D := by
    rw [List.filter_eq_self]
    intro dl hdl
    simp only [mvcc.Deliv.sent, Hkeep dl hdl, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    cases dl.1 <;> simp
  have hx63 : sint.Z x.rev < 2 ^ 63 := by word
  refine ⟨by word, by omega, ?_, by omega, by omega, h3, by omega⟩
  show ((v3rpc.sentEvsOf Dm w).map mvcc.RespM.evs).flatten = _
  rw [hfe, flatten_evs_filter, h1, hall, ← h2]
  congr 1
  exact List.map_congr_left (fun dl hdl => Hkeep dl hdl)

end chain

end client
end EtcdGrove
end Perennial
