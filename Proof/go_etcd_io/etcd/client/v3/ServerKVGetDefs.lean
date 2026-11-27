/-
**The wire's get and the server's answer, pure** (split out of `ServerKVGet.lean` on 2026-11-26, F6 of
`notes/etcd-dist-plan.md`, so that defs and proof modules can use them: that file is a linking module).
Lean-first, no Rocq counterpart.

* **The wire's get is the `Op`'s** (`wire_fields`, `wire_rangeSel`, `wire_sort`): the request
  `kv.Do` sends (`rangeWireOf o`) has the `Op`'s key, range, revision, limit, filters, flags; its
  sort fields are the `int32` values of the `Op`'s, the `Op`'s own for the values `getExact`
  allows, so the effective order and target are the `Op`'s.
* **The server answers as the model says** (`wire_not_cutEarly`, `wire_fastKeysOnly`,
  `wire_answer`): for a `getExact` get, `txn.srvRangeOk_rangeKvsOk` applies, the leases are not
  zeroed, and `More` is the model's.
* **A prefix get lists the state under the prefix** (`prefix_answer`, for a non-empty prefix:
  `isPrefixGet []` reads from `"\x00"` on and would leave out an empty key, which the server's
  model does not exclude; hence `pfx ≠ []`).
* The reply's key-values as the cache reads them (`kvValAt_of_kvIs`, `kvPtrsAt_of_kvsIs`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil errStrOk_of_statusErrOk)

theorem sext_small (x : w64) (h0 : 0 ≤ sint.Z x) (h1 : sint.Z x ≤ 4) :
    W64 (sint.Z (W32 (sint.Z x))) = x := by
  have : sint.Z (W32 (sint.Z x)) = sint.Z x := by word
  rw [this]; word

theorem sext_zero : W64 (sint.Z (W32 0)) = W64 0 := by word

theorem w32_zero_iff (x : w64) (h0 : 0 ≤ sint.Z x) (h1 : sint.Z x ≤ 4) :
    W32 (sint.Z x) = W32 0 ↔ x = W64 0 := by
  constructor
  · intro h
    rw [← sext_small x h0 h1, h]; word
  · intro h; subst h; word

/-- The wire's fields a get's answer reads are the `Op`'s. -/
theorem wire_fields (o : OpFull) :
    (rangeWireOf o).key = o.key ∧ (rangeWireOf o).base.rangeEnd = o.base.rangeEnd ∧
    (rangeWireOf o).base.rev = o.base.rev ∧ (rangeWireOf o).base.limit = o.base.limit ∧
    (rangeWireOf o).base.countOnly = o.base.countOnly ∧ (rangeWireOf o).keysOnly = o.keysOnly ∧
    (rangeWireOf o).base.serializable = o.base.serializable ∧
    (rangeWireOf o).base.minModRev = o.base.minModRev ∧
    (rangeWireOf o).base.maxModRev = o.base.maxModRev ∧
    (rangeWireOf o).base.minCreateRev = o.base.minCreateRev ∧
    (rangeWireOf o).base.maxCreateRev = o.base.maxCreateRev ∧ (rangeWireOf o).t = W64 1 := by
  simp [rangeWireOf, txn.rangeOpOf, op_simps]

theorem wire_rangeSel (o : OpFull) (s : List EtcdKv) : rangeSel s (rangeWireOf o) = rangeSel s o := by
  obtain ⟨h1, h2, -, -, -, -, -, h8, h9, h10, h11, -⟩ := wire_fields o
  have hf : kvFilterOk (rangeWireOf o) = kvFilterOk o := by
    funext v; unfold kvFilterOk; rw [h8, h9, h10, h11]
  simp only [rangeSel, rangeIn, h1, h2, hf]

theorem wire_sort (o : OpFull) (hx : o.getExact) :
    (rangeWireOf o).effSortOrder = o.effSortOrder ∧
      (o.effSortOrder ≠ W64 0 → (rangeWireOf o).sortTarget = o.sortTarget) ∧
      (rangeWireOf o).base.sortSet =
        decide ((rangeWireOf o).sortOrder ≠ W64 0 ∨ (rangeWireOf o).sortTarget ≠ W64 0) := by
  obtain ⟨-, -, -, ho0, ho1, ht0, ht1⟩ := hx
  have eo := sext_small o.sortOrder ho0 (by omega)
  have et := sext_small o.sortTarget ht0 ht1
  have zo := w32_zero_iff o.sortOrder ho0 (by omega)
  have zt := w32_zero_iff o.sortTarget ht0 ht1
  cases hs : o.base.sortSet
  · simp [rangeWireOf, txn.rangeOpOf, op_simps, sortOrderWire, sortTargetWire, OpFull.effSortOrder, hs, sext_zero]
  · simp only [rangeWireOf, txn.rangeOpOf, op_simps, sortOrderWire, sortTargetWire, OpFull.effSortOrder, hs, ↓reduceIte, eo, et, zo, zt]
    by_cases a : o.sortOrder = W64 0 <;> by_cases b : o.sortTarget = W64 0 <;> simp [a, b] <;>
      simp_all

theorem wire_sort_fields (o : OpFull) (hx : o.getExact) (hs : o.base.sortSet = true) :
    (rangeWireOf o).sortOrder = o.sortOrder ∧ (rangeWireOf o).sortTarget = o.sortTarget := by
  obtain ⟨-, -, -, ho0, ho1, ht0, ht1⟩ := hx
  have h1 := sext_small o.sortOrder ho0 (by omega)
  have h2 := sext_small o.sortTarget ht0 ht1
  constructor
  · show W64 (sint.Z (sortOrderWire o)) = _
    simp only [sortOrderWire, hs, ↓reduceIte]; exact h1
  · show W64 (sint.Z (sortTargetWire o)) = _
    simp only [sortTargetWire, hs, ↓reduceIte]; exact h2

theorem rangeLimit_nonpos (l : w64) (h : sint.Z l ≤ 0) :
    sint.Z (if 0 < sint.Z l ∧ sint.Z l < 2 ^ 63 - 1 then l + W64 1 else l) ≤ 0 := by
  rw [if_neg (by omega)]; exact h

theorem wire_not_cutEarly (o : OpFull) (hx : o.getExact) : ¬ txn.cutEarly (rangeWireOf o) := by
  rintro ⟨he, hlim⟩
  rw [(wire_sort o hx).1] at he
  have hc := hx.2.1
  cases hs : o.base.sortSet
  · simp [OpFull.effSortOrder, hs] at he
  obtain ⟨eo, et⟩ := wire_sort_fields o hx hs
  have el := (wire_fields o).2.2.2.1
  have key : sint.Z (if txn.isDefaultOrd (rangeWireOf o).sortTarget (rangeWireOf o).sortOrder = false ∨
      txn.hasRevFilters (rangeWireOf o) = true then W64 0 else (rangeWireOf o).base.limit) ≤ 0 := by
    rw [eo, et, el]
    unfold OpFull.effSortOrder at he
    simp only [hs, Bool.true_eq_false, ↓reduceIte] at he
    unfold txn.isDefaultOrd
    by_cases a : o.sortOrder = W64 0 <;> by_cases b : o.sortTarget = W64 0
    · simp [a, b] at he
    · have hl : ¬ 0 < sint.Z o.base.limit := fun h => hc ⟨hs, b, a, h⟩
      split
      · simp
      · omega
    · by_cases c : o.sortOrder = W64 1
      · simp [a, b, c] at he
      · rw [if_pos (Or.inl (by simp; exact ⟨a, fun _ => c⟩))]; simp
    · rw [if_pos (Or.inl (by simp; exact ⟨a, fun h => absurd h b⟩))]; simp
  have := rangeLimit_nonpos _ key
  unfold txn.rangeLimitOf at hlim
  exact absurd hlim (by simp only [] at this ⊢; omega)

theorem wire_fastKeysOnly (o : OpFull) (hx : o.getExact) : txn.fastKeysOnly (rangeWireOf o) = false := by
  simp [txn.fastKeysOnly, (wire_fields o).2.2.2.2.2.1, hx.1]

theorem wire_rangeKvsOk (o : OpFull) (hx : o.getExact) (sel kvs : List EtcdKv)
    (h : rangeKvsOk (rangeWireOf o) sel kvs) : rangeKvsOk o sel kvs := by
  obtain ⟨he, ht, -⟩ := wire_sort o hx
  obtain ⟨-, -, -, el, ec, ek, -⟩ := wire_fields o
  obtain ⟨l, hp, h0, h1, h2, hk⟩ := h
  rw [he] at h0 h1 h2
  refine ⟨l, hp, h0, fun e => ?_, fun e => ?_, ?_⟩
  · rw [← ht (by rw [e]; decide)]; exact h1 e
  · rw [← ht (by rw [e]; decide)]; exact h2 e
  · rw [hk, el, ec, ek]

/-- **The server's answer to the wire's get is the model's answer to the `Op`'s** (`getExact`):
its key-values are `rangeKvsOk` of the `Op`'s selection, and `More` is the model's. -/
theorem wire_answer (o : OpFull) (hx : o.getExact) (st kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk (rangeWireOf o) st kvs more) :
    rangeKvsOk o (rangeSel st o) kvs ∧
      more = (!o.base.countOnly && decide (0 < sint.Z o.base.limit) &&
        decide (sint.Z o.base.limit < ((rangeSel st o).length : Int))) := by
  obtain ⟨-, -, -, el, ec, -⟩ := wire_fields o
  obtain ⟨kvs', hok, hk, hm⟩ := txn.srvRangeOk_rangeKvsOk (rangeWireOf o) st kvs more
    (wire_sort o hx).2.2 h (wire_not_cutEarly o hx)
  rw [wire_fastKeysOnly o hx] at hk
  have hk' : kvs = kvs' := by
    rw [hk]; conv => rhs; rw [← List.map_id kvs']
    congr 1
  subst hk'
  rw [wire_rangeSel] at hok hm
  refine ⟨wire_rangeKvsOk o hx _ _ hok, ?_⟩
  cases hco : o.base.countOnly
  · rw [ec, el, hco] at hm
    rw [hm rfl hx.2.2.1]
    simp
  · obtain ⟨l, ⟨hperm, -⟩, hmore, -⟩ := h
    have hpre : txn.srvPre (rangeWireOf o) st = [] := by
      unfold txn.srvPre; rw [ec, hco]; rfl
    rw [hpre] at hperm
    have := List.Perm.eq_nil hperm
    subst this
    rw [hmore]; simp [txn.srvMore, hco]; omega

/-- **A prefix get's answer is the state under the prefix** (a non-empty prefix: for the empty
one, `isPrefixGet` reads from `"\x00"` on, which leaves out an empty key). -/
theorem prefix_answer (pfx : GoString) (o : OpFull) (hp : o.isPrefixGet pfx = true)
    (hne : pfx ≠ []) (st kvs : List EtcdKv) (h : rangeKvsOk o (rangeSel st o) kvs) :
    kvs = txn.underPfx pfx st ∧ o.base.rev = W64 0 ∧ o.base.serializable = o.base.serializable := by
  simp only [OpFull.isPrefixGet, hne, ↓reduceIte, decide_eq_true_eq] at hp
  obtain ⟨-, hk, hc, hs, hl, hr, h1, h2, h3, h4, hkey, hre⟩ := hp
  obtain ⟨l, hperm, h0, -, -, hkv⟩ := h
  have he : o.effSortOrder = W64 0 := by simp [OpFull.effSortOrder, hs]
  rw [h0 he] at hkv
  refine ⟨?_, hr, rfl⟩
  rw [hkv, hc, hk, hl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have : (0 : Int) < sint.Z (W64 0) ↔ False := by simp
  simp only [this, ↓reduceIte, List.map_id']
  unfold rangeSel rangeIn txn.underPfx
  rw [List.filter_filter]
  apply List.filter_congr
  intro v _
  rw [hkey, hre]
  have hf : kvFilterOk o v = true := by simp [kvFilterOk, h1, h2, h3, h4]
  rw [hf, Bool.true_and]
  by_cases hv : pfx <+: v.key
  · simp [hv, (concurrency.inRange_prefix pfx v.key hne).2 hv]
  · have : inRange pfx (prefixRangeEnd pfx) v.key = false := by
      cases h' : inRange pfx (prefixRangeEnd pfx) v.key
      · rfl
      · exact absurd ((concurrency.inRange_prefix pfx v.key hne).1 h') hv
    simp [hv, this]

theorem isPrefixGet_rev (pfx : GoString) (o : OpFull) (hp : o.isPrefixGet pfx = true) :
    o.base.rev = W64 0 := by
  simp only [OpFull.isPrefixGet, decide_eq_true_eq] at hp
  exact hp.2.2.2.2.2.1

section kvs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The server's key-value (`txn.kvIs`) is the client's (`kvValAt`): the same fields. -/
theorem kvValAt_of_kvIs (p : Loc) (v : EtcdKv) : txn.kvIs (GF := GF) p v ⊢ kvValAt p v := by
  unfold txn.kvIs kvValAt
  iintro ⟨%ks, %vs, #Hk, #Hks, #Hc, #Hm, #Hver, #Hv, #Hvs, #Hl, -⟩
  iexists ks, vs
  iframe #

/-- The server's key-values (`txn.kvsIs`) are the client's (`kvPtrsAt`): the same fields. -/
theorem kvPtrsAt_of_kvsIs (ps : List Loc) (kvs : List EtcdKv) :
    txn.kvsIs (GF := GF) ps kvs ⊢ kvPtrsAt ps kvs := by
  unfold txn.kvsIs kvPtrsAt
  iintro ⟨%Hl, #H⟩
  isplitr
  · ipureintro; exact Hl
  iintro !> %i %p %v %hp %hv
  iapply kvValAt_of_kvIs
  iapply H $$ %i %p %v %hp %hv

end kvs

end client
end EtcdGrove
end Perennial
