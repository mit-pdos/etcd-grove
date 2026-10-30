/-
Lemmas about `Mutex`'s gets, transactions and deletes (`InvMutex.lean`): what the responses of
`ownerOp`, `lastCreateOp`, `keyOp` list; `tryAcquire`'s transaction; a single-key delete; the
step of `Lock` from `waitDeletes` to the ownership fact. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutex
public import Proof.go_etcd_io.etcd.client.v3.PrefixRange

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

/-! ## The mutex's gets -/

theorem ownerOp_fields (pfx : GoString) (hp : pfx ≠ []) :
    (ownerOp pfx).key = pfx ∧ (ownerOp pfx).base.rangeEnd = prefixRangeEnd pfx ∧
    (ownerOp pfx).effSortOrder = W64 1 ∧ (ownerOp pfx).sortTarget = W64 2 ∧
    (ownerOp pfx).base.limit = W64 1 ∧ (ownerOp pfx).base.countOnly = false ∧
    (ownerOp pfx).keysOnly = false ∧ (ownerOp pfx).base.minModRev = W64 0 ∧
    (ownerOp pfx).base.maxModRev = W64 0 ∧ (ownerOp pfx).base.minCreateRev = W64 0 ∧
    (ownerOp pfx).base.maxCreateRev = W64 0 := by
  simp [ownerOp, lastCreateOp, keyOp, op_simps, hp, OpFull.effSortOrder]

theorem lastCreateOp_fields (pfx : GoString) (n : w64) (hp : pfx ≠ []) :
    (lastCreateOp pfx n).key = pfx ∧ (lastCreateOp pfx n).base.rangeEnd = prefixRangeEnd pfx ∧
    (lastCreateOp pfx n).effSortOrder = W64 2 ∧ (lastCreateOp pfx n).sortTarget = W64 2 ∧
    (lastCreateOp pfx n).base.limit = W64 1 ∧ (lastCreateOp pfx n).base.countOnly = false ∧
    (lastCreateOp pfx n).keysOnly = false ∧ (lastCreateOp pfx n).base.minModRev = W64 0 ∧
    (lastCreateOp pfx n).base.maxModRev = W64 0 ∧ (lastCreateOp pfx n).base.minCreateRev = W64 0 ∧
    (lastCreateOp pfx n).base.maxCreateRev = n := by
  simp [ownerOp, lastCreateOp, keyOp, op_simps, hp, OpFull.effSortOrder]

theorem keyOp_fields (key : GoString) :
    (keyOp key).key = key ∧ (keyOp key).base.rangeEnd = [] ∧
    (keyOp key).effSortOrder = W64 0 ∧
    (keyOp key).base.limit = W64 0 ∧ (keyOp key).base.countOnly = false ∧
    (keyOp key).keysOnly = false ∧ (keyOp key).base.minModRev = W64 0 ∧
    (keyOp key).base.maxModRev = W64 0 ∧ (keyOp key).base.minCreateRev = W64 0 ∧
    (keyOp key).base.maxCreateRev = W64 0 := by
  simp [ownerOp, lastCreateOp, keyOp, op_simps, OpFull.effSortOrder]

theorem rangeIn_key (key : GoString) (o : OpFull) (s : List EtcdKv)
    (hk : o.key = key) (he : o.base.rangeEnd = []) (v : EtcdKv) :
    v ∈ rangeIn s o ↔ v ∈ s ∧ v.key = key := by
  unfold rangeIn; rw [hk, he]; simp [inRange]

theorem kvFilterOk_zero (o : OpFull) (v : EtcdKv) (h1 : o.base.minModRev = W64 0)
    (h2 : o.base.maxModRev = W64 0) (h3 : o.base.minCreateRev = W64 0)
    (h4 : o.base.maxCreateRev = W64 0) : kvFilterOk o v = true := by
  simp [kvFilterOk, h1, h2, h3, h4]

theorem filter_key_single (s : List EtcdKv) (hs : (s.map EtcdKv.key).Pairwise go.GoStringLt)
    (key : GoString) (p : EtcdKv → Bool) (hp : ∀ w, p w = true ↔ w.key = key)
    (v : EtcdKv) (hv : v ∈ s) (hk : v.key = key) : s.filter p = [v] := by
  induction s with
  | nil => simp at hv
  | cons x xs ih =>
    rw [List.map_cons, List.pairwise_cons] at hs
    rcases List.mem_cons.1 hv with rfl | hv'
    · rw [List.filter_cons_of_pos ((hp v).2 hk), List.filter_eq_nil_iff.2]
      intro w hw hpw
      have := hs.1 w.key (List.mem_map_of_mem hw)
      rw [hk, (hp w).1 hpw] at this; exact go.goStringLt_irrefl _ this
    · have hx : ¬ p x = true := by
        intro hpx
        have := hs.1 v.key (List.mem_map_of_mem hv')
        rw [hk, (hp x).1 hpx] at this; exact go.goStringLt_irrefl _ this
      rw [List.filter_cons_of_neg hx]
      exact ih hs.2 hv'

theorem rangeIn_prefix_all (pfx : GoString) (o : OpFull) (s : List EtcdKv) (hp : pfx ≠ [])
    (hwf : EtcdStateWf pfx s) (hk : o.key = pfx) (he : o.base.rangeEnd = prefixRangeEnd pfx) :
    rangeIn s o = s := by
  unfold rangeIn; rw [hk, he, List.filter_eq_self]
  intro v hv; exact (inRange_prefix pfx v.key hp).2 (hwf.2 v hv)

theorem ownerOp_t (pfx : GoString) : (ownerOp pfx).t = W64 1 := by
  by_cases h : pfx = [] <;> simp [ownerOp, lastCreateOp, keyOp, op_simps, h]

theorem ownerOp_under (pfx : GoString) (hp : pfx ≠ []) :
    KeyRangeUnder pfx (ownerOp pfx).key (ownerOp pfx).base.rangeEnd := by
  obtain ⟨hk, he, -⟩ := ownerOp_fields pfx hp
  rw [hk, he]
  exact keyRangeUnder_prefix pfx hp

theorem ownerOp_txnOpOf (pfx : GoString) : txnOpOf (ownerOp pfx) = some (.get (ownerOp pfx)) := by
  by_cases h : pfx = [] <;> simp [ownerOp, lastCreateOp, keyOp, op_simps, h]

theorem ownerOp_not_panics (_pfx : GoString) : ¬ opGetPanics (withTopM (W64 2) (W64 1)) := by
  simp [ownerOp, lastCreateOp, keyOp, op_simps, opGetPanics]

/-! ### The gets' sizes (2026-10-30: each fits a gRPC message, `opSizeOk`) -/

/-- The owner get of a prefix of at most `2 ^ 27` bytes. -/
theorem ownerOp_size {pfx : GoString} (h : pfx.length ≤ 2 ^ 27) : opSizeOk (ownerOp pfx) :=
  opSizeOk_opGetModel (K := 2 ^ 27) (E := 2 ^ 27) (V := 0)
    (optsKeep_cons (withPrefixM_keep (by decide) (Nat.le_refl _))
      (optsKeep_cons (withSortM_keep _ _) (optsKeep_cons (withLimitM_keep _)
        (optsKeep_nil _ _ _)))) h (by decide)

/-- `waitDeletes`' get of a prefix of at most `2 ^ 27` bytes. -/
theorem lastCreateOp_size {pfx : GoString} (n : w64) (h : pfx.length ≤ 2 ^ 27) :
    opSizeOk (lastCreateOp pfx n) :=
  opSizeOk_opGetModel (K := 2 ^ 27) (E := 2 ^ 27) (V := 0)
    (optsKeep_cons (withPrefixM_keep (by decide) (Nat.le_refl _))
      (optsKeep_cons (withSortM_keep _ _) (optsKeep_cons (withLimitM_keep _)
        (optsKeep_cons (withMaxCreateRevM_keep _) (optsKeep_nil _ _ _))))) h (by decide)

/-- The single-key get of a key of at most `2 ^ 28` bytes. -/
theorem keyOp_size {key : GoString} (h : key.length ≤ 2 ^ 28) : opSizeOk (keyOp key) :=
  opSizeOk_opGetModel (K := 2 ^ 28) (E := 0) (V := 0) (optsKeep_nil _ _ _) h (by decide)

/-- **The owner get** (`OpGet(pfx, WithFirstCreate()...)`) on a state with some key lists exactly
one key, the one with the smallest create revision. -/
theorem ownerOp_kvs (pfx key : GoString) (rev : w64) (s kvs : List EtcdKv) (hp : pfx ≠ [])
    (hwf : EtcdStateWf pfx s) (hk : HasKeyAt key rev s)
    (h : rangeKvsOk (ownerOp pfx) (rangeSel s (ownerOp pfx)) kvs) :
    ∃ w, kvs = [w] ∧ w ∈ s ∧ ∀ v ∈ s, sint.Z w.createRev ≤ sint.Z v.createRev := by
  obtain ⟨hkey, he, hso, hst, hl, hc, hko, h1, h2, h3, h4⟩ := ownerOp_fields pfx hp
  have hsel : rangeSel s (ownerOp pfx) = s := by
    unfold rangeSel; rw [rangeIn_prefix_all pfx _ s hp hwf hkey he, List.filter_eq_self]
    intro v _; exact kvFilterOk_zero _ v h1 h2 h3 h4
  rw [hsel] at h
  obtain ⟨l, hperm, -, hsorted, -, rfl⟩ := h
  have hsorted := hsorted hso
  rw [hst] at hsorted
  obtain ⟨v0, hv0, -⟩ := hk
  cases l with
  | nil => exact absurd (hperm.symm.subset hv0) (by simp)
  | cons w l' =>
    refine ⟨w, by simp [hc, hl, hko], hperm.subset (by simp), ?_⟩
    intro v hv
    rcases List.mem_cons.1 (hperm.symm.subset hv) with rfl | hv'
    · exact Int.le_refl _
    · have := (List.pairwise_cons.1 hsorted).1 v hv'; simpa [kvLeBy] using this

theorem lastCreateOp_t (pfx : GoString) (n : w64) : (lastCreateOp pfx n).t = W64 1 := by
  by_cases h : pfx = [] <;> simp [ownerOp, lastCreateOp, keyOp, op_simps, h]

theorem lastCreateOp_under (pfx : GoString) (n : w64) (hp : pfx ≠ []) :
    KeyRangeUnder pfx (lastCreateOp pfx n).key (lastCreateOp pfx n).base.rangeEnd := by
  obtain ⟨hk, he, -⟩ := lastCreateOp_fields pfx n hp
  rw [hk, he]
  exact keyRangeUnder_prefix pfx hp

theorem lastCreateOp_rev (pfx : GoString) (n : w64) :
    (lastCreateOp pfx n).base.rev = W64 0 ∧ (lastCreateOp pfx n).base.serializable = false ∧
      (lastCreateOp pfx n).isPrefixGet pfx = false := by
  by_cases h : pfx = [] <;> simp [ownerOp, lastCreateOp, keyOp, op_simps, h, OpFull.isPrefixGet]

theorem lastCreateOp_not_panics (n : w64) :
    ¬ opGetPanics (withTopM (W64 2) (W64 2) ++ [withMaxCreateRevM n]) := by
  simp [ownerOp, lastCreateOp, keyOp, op_simps, opGetPanics]

/-- **`waitDeletes`'s get** (`OpGet(pfx, WithLastCreate()..., WithMaxCreateRev(n))`, `n ≥ 0`; `0`
is no filter): nothing means no key was created at or before `n`; anything listed is in the
state. -/
theorem lastCreateOp_kvs (pfx : GoString) (n : w64) (s kvs : List EtcdKv) (hp : pfx ≠ [])
    (hwf : EtcdStateWf pfx s)
    (h : rangeKvsOk (lastCreateOp pfx n) (rangeSel s (lastCreateOp pfx n)) kvs) :
    (kvs = [] → ∀ v ∈ s, sint.Z n < sint.Z v.createRev) ∧ ∀ w ∈ kvs, w ∈ s := by
  obtain ⟨hkey, he, hso, hst, hl, hc, hko, h1, h2, h3, h4⟩ := lastCreateOp_fields pfx n hp
  have hmem : ∀ v, v ∈ rangeSel s (lastCreateOp pfx n) ↔
      v ∈ s ∧ (n = W64 0 ∨ sint.Z v.createRev ≤ sint.Z n) := by
    intro v
    unfold rangeSel; rw [rangeIn_prefix_all pfx _ s hp hwf hkey he, List.mem_filter]
    rw [and_congr_right_iff]; intro _
    by_cases hn0 : n = W64 0
    · subst hn0; simp only [kvFilterOk, h1, h2, h3, h4]; simp
    · simp only [kvFilterOk, h1, h2, h3, h4, hn0]; simp [hn0]
  obtain ⟨l, hperm, -, -, -, rfl⟩ := h
  simp only [hc, hl, hko] at *
  refine ⟨fun h0 v hv => ?_, fun w hw => ?_⟩
  · refine Int.lt_of_not_ge fun hle => ?_
    have := hperm.symm.subset ((hmem v).2 ⟨hv, Or.inr hle⟩)
    cases l with
    | nil => simp at this
    | cons x l' => simp at h0
  · simp at hw
    have := List.mem_of_mem_take hw
    exact ((hmem w).1 (hperm.subset this)).1

theorem keyOp_t (key : GoString) : (keyOp key).t = W64 1 ∧ (keyOp key).key = key ∧
    (keyOp key).base.rangeEnd = [] ∧ (keyOp key).base.rev = W64 0 ∧
    (keyOp key).base.serializable = false := by
  simp [ownerOp, lastCreateOp, keyOp, op_simps]

theorem keyOp_isPrefixGet (pfx key : GoString) : (keyOp key).isPrefixGet pfx = false := by
  by_cases h : pfx = [] <;> simp [ownerOp, lastCreateOp, keyOp, op_simps, h, OpFull.isPrefixGet, prefixRangeEnd_ne_nil]

theorem keyOp_not_panics : ¬ opGetPanics ([] : List (OpFull → OpFull)) := by
  simp [ownerOp, lastCreateOp, keyOp, op_simps, opGetPanics]

theorem keyOp_txnOpOf (key : GoString) : txnOpOf (keyOp key) = some (.get (keyOp key)) := by
  simp [ownerOp, lastCreateOp, keyOp, op_simps]

/-- **A single-key get** (`OpGet(key)`) lists the key's key-value, if present, and nothing
otherwise. -/
theorem keyOp_kvs (pfx key : GoString) (s kvs : List EtcdKv) (hwf : EtcdStateWf pfx s)
    (h : rangeKvsOk (keyOp key) (rangeSel s (keyOp key)) kvs) :
    ((∀ v ∈ s, v.key ≠ key) → kvs = []) ∧ (∀ v ∈ s, v.key = key → kvs = [v]) := by
  obtain ⟨hkey, he, hso, hl, hc, hko, h1, h2, h3, h4⟩ := keyOp_fields key
  have hmem : ∀ v, v ∈ rangeSel s (keyOp key) ↔ v ∈ s ∧ v.key = key := by
    intro v
    unfold rangeSel; rw [List.mem_filter, rangeIn_key key _ s hkey he]
    simp only [kvFilterOk_zero _ v h1 h2 h3 h4, and_true]
  obtain ⟨l, -, hl0, -, -, rfl⟩ := h
  rw [hl0 hso]
  simp only [hc, hl, hko]
  simp
  refine ⟨fun hn => ?_, fun v hv hvk => ?_⟩
  · rw [List.eq_nil_iff_forall_not_mem]
    intro v hv; exact hn v ((hmem v).1 hv).1 ((hmem v).1 hv).2
  · unfold rangeSel
    have : rangeIn s (keyOp key) = [v] := by
      unfold rangeIn
      exact filter_key_single s hwf.1 key _ (fun w => by rw [hkey, he]; simp [inRange]) v hv hvk
    rw [this]; simp [kvFilterOk_zero _ v h1 h2 h3 h4]

/-! ## `tryAcquire`'s transaction -/

/-- `OpPut(key, "", WithLease(id))` in a transaction. -/
theorem putOp_txnOpOf (key : GoString) (id : w64) :
    txnOpOf (opPutModel key [] [withLeaseM id]) = some (.put key [] id) := by
  simp [ownerOp, lastCreateOp, keyOp, op_simps]

theorem putOp_not_panics (key : GoString) (id : w64) :
    ¬ (opPutModel key [] [withLeaseM id]).putPanics := by
  simp [ownerOp, lastCreateOp, keyOp, op_simps, OpFull.putPanics]

theorem acquireTxn_under (pfx key : GoString) (lease : w64) (hp : pfx ≠ []) (hk : pfx <+: key) :
    (acquireTxn pfx key lease).Under pfx := by
  obtain ⟨hkk, hke, -⟩ := keyOp_fields key
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    simp only [acquireTxn, List.mem_singleton] at hc
    subst hc
    exact keyRangeUnder_key pfx key hk
  · intro op hop
    simp only [acquireTxn, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl
    · exact hk
    · exact ownerOp_under pfx hp
  · intro op hop
    simp only [acquireTxn, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl
    · show KeyRangeUnder pfx (keyOp key).key (keyOp key).base.rangeEnd
      rw [hkk, hke]; exact keyRangeUnder_key pfx key hk
    · exact ownerOp_under pfx hp

/-- `tryAcquire`'s comparison holds exactly when `key` is absent (create revisions positive). -/
theorem acquire_cmp_absent (key : GoString) (s : List EtcdKv) (h : ∀ v ∈ s, v.key ≠ key) :
    cmpHolds s (compareM (cmpKeyM .create key) .eq (.num (W64 0))) = true := by
  have : s.filter (fun v => inRange key [] v.key) = [] := by
    rw [List.filter_eq_nil_iff]; intro v hv; simpa [inRange] using h v hv
  simp [cmpHolds, compareM, cmpKeyM, this, cmpKv, zeroKv, int64Cmp, cmpSign, CmpOp.holds]

theorem acquire_cmp_present (key : GoString) (s : List EtcdKv)
    (hpos : ∀ v ∈ s, 0 < sint.Z v.createRev) (h : ∃ v ∈ s, v.key = key) :
    cmpHolds s (compareM (cmpKeyM .create key) .eq (.num (W64 0))) = false := by
  obtain ⟨v, hv, hvk⟩ := h
  have hne : s.filter (fun v => inRange key [] v.key) ≠ [] := by
    intro e
    have : v ∈ s.filter (fun v => inRange key [] v.key) := by
      rw [List.mem_filter]; exact ⟨hv, by simp [inRange, hvk]⟩
    rw [e] at this; simp at this
  simp only [cmpHolds, compareM, cmpKeyM, hne, ite_false]
  rw [List.all_eq_false]
  refine ⟨v, List.mem_filter.2 ⟨hv, by simp [inRange, hvk]⟩, ?_⟩
  have h1 := hpos v hv
  have h2 : v.createRev ≠ W64 0 := by intro e; rw [e] at h1; simp at h1
  have h3 : ¬ sint.Z v.createRev < sint.Z (W64 0) := by simp; omega
  simp only [cmpKv, int64Cmp, cmpSign, CmpOp.holds, h2, h3, decide_false]
  decide

theorem btInsert_self_mem {V : Type} {less : V → V → Prop} [DecidableRel less] (v : V)
    (items : List V) : v ∈ btInsert less v items := by
  induction items with
  | nil => simp [btInsert]
  | cons w ws ih =>
    unfold btInsert
    split
    · exact List.mem_cons_of_mem _ ih
    · split <;> simp

/-- The comparison held: `key` was absent (etcd's create revisions are positive), the transaction
put it (a write, at `r`) and then got the owner on the new state. -/
theorem acquireTxn_then (pfx key : GoString) (lease r : w64) (s : List EtcdKv)
    (hwf : EtcdStateWf pfx s) (hk : pfx <+: key) (hpos : ∀ v ∈ s, 0 < sint.Z v.createRev)
    (h : (runTxn r s (acquireTxn pfx key lease)).1 = true) :
    (runTxn r s (acquireTxn pfx key lease)).2.1 = putKv r key [] lease s ∧
    txnWrote (runTxn r s (acquireTxn pfx key lease)).2.2 = true ∧
    (runTxn r s (acquireTxn pfx key lease)).2.2 =
      [.put, .range (rangeSel (putKv r key [] lease s) (ownerOp pfx))
        (rangeIn (putKv r key [] lease s) (ownerOp pfx)).length] ∧
    EtcdStateWf pfx (putKv r key [] lease s) ∧ HasKeyAt key r (putKv r key [] lease s) := by
  have habs : ∀ v ∈ s, v.key ≠ key := by
    intro v hv hvk
    have := acquire_cmp_present key s hpos ⟨v, hv, hvk⟩
    have h' : (acquireTxn pfx key lease).cmps.all (cmpHolds s) = true := h
    simp only [acquireTxn, List.all_cons, List.all_nil, Bool.and_true] at h'
    rw [this] at h'; cases h'
  have hok : (acquireTxn pfx key lease).cmps.all (cmpHolds s) = true := by
    simp only [acquireTxn, List.all_cons, List.all_nil, Bool.and_true]
    exact acquire_cmp_absent key s habs
  have e : runTxn r s (acquireTxn pfx key lease) = (true, putKv r key [] lease s,
      [.put, .range (rangeSel (putKv r key [] lease s) (ownerOp pfx))
        (rangeIn (putKv r key [] lease s) (ownerOp pfx)).length]) := by
    simp only [runTxn, hok, TxnModel.branch, ite_true]
    simp [acquireTxn, runOps, applyTxnOp]
  rw [e]
  have hfind : s.find? (fun v => decide (v.key = key)) = none := by
    rw [List.find?_eq_none]; intro v hv; simpa using habs v hv
  refine ⟨rfl, rfl, rfl, ⟨?_, ?_⟩, ?_⟩
  · unfold putKv; rw [hfind]
    have h0 : s.Pairwise etcdKvLess := (List.pairwise_map (f := EtcdKv.key) (R := go.GoStringLt)).1 hwf.1
    exact (List.pairwise_map (f := EtcdKv.key) (R := go.GoStringLt)).2
      (btInsert_sorted etcdKvLess_swo h0)
  · unfold putKv; rw [hfind]
    intro v hv
    rcases btInsert_mem hv with rfl | hv
    · exact hk
    · exact hwf.2 v hv
  · unfold putKv; rw [hfind]
    exact ⟨_, btInsert_self_mem _ _, rfl, rfl⟩

/-- The comparison failed: `key` was present, the transaction wrote nothing and got `key` and
the owner. -/
theorem acquireTxn_else (pfx key : GoString) (lease r : w64) (s : List EtcdKv)
    (h : (runTxn r s (acquireTxn pfx key lease)).1 = false) :
    (∃ v ∈ s, v.key = key) ∧ (runTxn r s (acquireTxn pfx key lease)).2.1 = s ∧
    txnWrote (runTxn r s (acquireTxn pfx key lease)).2.2 = false ∧
    (runTxn r s (acquireTxn pfx key lease)).2.2 =
      [.range (rangeSel s (keyOp key)) (rangeIn s (keyOp key)).length,
       .range (rangeSel s (ownerOp pfx)) (rangeIn s (ownerOp pfx)).length] := by
  have hpres : ∃ v ∈ s, v.key = key := by
    refine Classical.byContradiction fun hn => ?_
    have habs : ∀ v ∈ s, v.key ≠ key := fun v hv hvk => hn ⟨v, hv, hvk⟩
    have := acquire_cmp_absent key s habs
    have h' : (acquireTxn pfx key lease).cmps.all (cmpHolds s) = false := h
    simp only [acquireTxn, List.all_cons, List.all_nil, Bool.and_true] at h'
    rw [this] at h'; cases h'
  have hok : (acquireTxn pfx key lease).cmps.all (cmpHolds s) = false := h
  have e : runTxn r s (acquireTxn pfx key lease) = (false, s,
      [.range (rangeSel s (keyOp key)) (rangeIn s (keyOp key)).length,
       .range (rangeSel s (ownerOp pfx)) (rangeIn s (ownerOp pfx)).length]) := by
    simp only [runTxn, hok, TxnModel.branch]
    simp [acquireTxn, runOps, applyTxnOp]
  rw [e]
  exact ⟨hpres, rfl, rfl, rfl⟩

/-! ## Deletes -/

theorem deleteOp_not_panics (key : GoString) : ¬ opDeletePanics key [] := by
  simp [ownerOp, lastCreateOp, keyOp, op_simps, opDeletePanics, opGetPanics, OpFull.deletePanics]

theorem deleteOp_fields (key : GoString) :
    (opDeleteModel key []).key = key ∧ (opDeleteModel key []).base.rangeEnd = [] := by
  simp [ownerOp, lastCreateOp, keyOp, op_simps]

section iprop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]

/-- After a single-key delete (wrote or not), the key is absent. -/
theorem deleteTxn_absent (pfx key : GoString) (r : w64) (s : List EtcdKv) :
    txnStates (GF := GF) pfx r s (runTxn r s (deleteTxn (opDeleteModel key []))).2.1
      (txnWrote (runTxn r s (deleteTxn (opDeleteModel key []))).2.2) ⊢ etcdAbsent pfx key r := by
  obtain ⟨hk, he⟩ := deleteOp_fields key
  have habs : ∀ v ∈ (runTxn r s (deleteTxn (opDeleteModel key []))).2.1, v.key ≠ key := by
    intro v hv
    simp only [runTxn, deleteTxn, TxnModel.branch, List.all_nil, ite_true, runOps, applyTxnOp,
      hk, he] at hv
    simp [inRange] at hv
    exact hv.2
  unfold txnStates etcdAbsent
  split
  · iintro ⟨-, #H⟩
    iexists _
    iframe H
    ipureintro; exact habs
  · rename_i hw
    rw [show (runTxn r s (deleteTxn (opDeleteModel key []))).2.1 = s from
      runOps_noWrite r s _ (Bool.eq_false_iff.2 hw)] at habs
    iintro #H
    iexists s
    iframe H
    ipureintro; exact habs

/-- **`Lock`'s last step.** `myKey` was created at `rev ≤ r ≤ R0`, `waitDeletes` saw no key
created before `rev` at `R0`, and `myKey` is present at `R ≥ R0`: no key at `R` was created before
`rev` (one would have been present at `R0`: `etcdState_create_persist`), so `myKey` holds the lock
at `R` if it still has create revision `rev`, and was re-created otherwise. -/
theorem lock_final (pfx key : GoString) (rev r R0 R : w64) (s0 s : List EtcdKv)
    (hrev : 0 < sint.Z rev) (h1 : sint.Z rev ≤ sint.Z r) (h2 : sint.Z r ≤ sint.Z R0)
    (h3 : sint.Z R0 ≤ sint.Z R) (hn : ∀ v ∈ s0, sint.Z (rev - W64 1) < sint.Z v.createRev)
    (hk : ∃ v ∈ s, v.key = key) :
    etcdState (GF := GF) R0 pfx s0 ∗ etcdState R pfx s ⊢
      ⌜LockedState key rev s ∨ RecreatedState key rev s⌝ := by
  iintro ⟨Hs0, Hs⟩
  ihave %Hp := etcdState_create_persist R R0 pfx s s0 $$ [$Hs $Hs0]
  ipureintro
  have hr1 : sint.Z (rev - W64 1) = sint.Z rev - 1 := by word
  have hmin : ∀ v ∈ s, sint.Z rev ≤ sint.Z v.createRev := by
    intro v hv
    refine Int.not_lt.1 fun hlt => ?_
    obtain ⟨v', hv', -, hc⟩ := Hp v hv (by omega) h3
    have := hn v' hv'
    rw [hc] at this; omega
  obtain ⟨v, hv, hvk⟩ := hk
  by_cases hc : v.createRev = rev
  · exact Or.inl ⟨⟨v, hv, hvk, hc⟩, hmin⟩
  · refine Or.inr ⟨⟨v, hv, hvk, ?_⟩, hmin⟩
    have := hmin v hv
    have : sint.Z v.createRev ≠ sint.Z rev := fun e => hc (by word)
    omega

end iprop

end concurrency
end EtcdGrove
end Perennial
