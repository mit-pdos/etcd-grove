/-
Lean-first (no Rocq counterpart).

# `kubernetes.Client.List`'s range is a page of the list (pure; k8s 7e-1, the Draft's §3.2)

`List` reads `[start, GetPrefixRangeEnd prefix)` with `WithLimit(opts.Limit)` and
`WithRev(opts.Revision)`, from a start key under the prefix; `srvRangeOk_page` shows the server's
answer to that range (`txn.srvRangeOk`, `txn.srvCount` with the total) is `pageKvsL`'s page and
count. `prefix_not_lt` moved here from the store's `ListPages` (k8s 7e-1).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Defs
public import Proof.go_etcd_io.etcd.client.v3.PrefixRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

section pure
variable [GooseExts]

/-- A prefix of a string is not above it. -/
theorem prefix_not_lt : ∀ (a b : GoString), a <+: b → ¬ go.GoStringLt b a
  | [], _, _ => go.goStringLt_not_nil _
  | x :: xs, b, h => by
    obtain ⟨t, rfl⟩ := h
    rw [List.cons_append, go.goStringLt_cons_iff]
    rintro (h | ⟨-, h⟩)
    · exact Int.lt_irrefl _ h
    · exact prefix_not_lt xs (xs ++ t) (List.prefix_append _ _) h

/-- Below a key not above which is `b`, below `b`'s prefix-free lower bound `a`: if `a ≤ b` and
`k ≥ b` then `k ≥ a`. -/
theorem not_lt_of_not_lt {a b k : GoString} (hab : ¬ go.GoStringLt b a)
    (hkb : ¬ go.GoStringLt k b) : ¬ go.GoStringLt k a := by
  intro hka
  by_cases hba : a = b
  · subst hba; exact hkb hka
  · by_cases hlt : go.GoStringLt a b
    · exact hkb (go.goStringLt_trans hka hlt)
    · exact hba (go.goStringLt_eq_of_not_lt hlt hab)

/-- A request range with a non-empty end, from `x`: the keys not below `x` in the range from the
empty key. -/
theorem inRange_split (x e k : GoString) (he : e ≠ []) :
    inRange x e k = (!decide (go.GoStringLt k x) && inRange [] e k) := by
  unfold inRange
  by_cases h0 : e = [W8 0]
  · simp [h0, go.goStringLt_not_nil]
  · simp only [he, h0, ↓reduceIte]; simp [go.goStringLt_not_nil]

/-- **`List`'s range from a start key under the prefix** selects the prefix's keys not below the
start key. -/
theorem inRange_page (pfx start k : GoString) (hst : pfx <+: start) :
    inRange start (prefixRangeEnd pfx) k =
      (kInScope pfx true k && !decide (go.GoStringLt k start)) := by
  have he := concurrency.prefixRangeEnd_ne_nil pfx
  rw [inRange_split start _ k he]
  simp only [kInScope, ↓reduceIte]
  by_cases hp : pfx = []
  · subst hp
    have h0 : prefixRangeEnd ([] : GoString) = [W8 0] := rfl
    simp [h0, inRange, go.goStringLt_not_nil]
  have hpr := concurrency.inRange_prefix pfx k hp
  rw [inRange_split pfx _ k he] at hpr
  have hsp := prefix_not_lt pfx start hst
  cases hk : decide (go.GoStringLt k start) <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hk
  · have hkp := not_lt_of_not_lt hsp hk
    simp only [hkp, decide_false, Bool.not_false, Bool.true_and] at hpr
    simp only [Bool.not_false, Bool.true_and, Bool.and_true]
    cases hb : inRange [] (prefixRangeEnd pfx) k
    · rw [hb] at hpr
      have : ¬ pfx <+: k := fun h => absurd (hpr.2 h) (by simp)
      simp [this]
    · rw [hb] at hpr
      simp [hpr.1 rfl]
  · simp

/-- `List`'s range on the wire: `OpGet(start, WithRange(GetPrefixRangeEnd(prefix)),
WithLimit(lim), WithRev(rev))`. -/
abbrev pageOp (pfx start : GoString) (rev lim : w64) : OpFull :=
  txn.rangeOpOf start (prefixRangeEnd pfx) rev lim (W32 0) (W32 0) false false false
    (W64 0) (W64 0) (W64 0) (W64 0)

theorem rangeWireOf_page (pfx start : GoString) (rev lim : w64) :
    rangeWireOf (opGetModel start [withRangeM (prefixRangeEnd pfx), withLimitM lim,
      withRevM rev]) = pageOp pfx start rev lim := rfl

/-- **`List`'s answer is a page** (the Draft's §3.2): the key-values of the server's answer to
`List`'s range are `pageKvsL`'s, and its count (with the total) the page's count. -/
theorem srvRangeOk_page (pfx start : GoString) (rev lim : w64) (s : KVStore)
    (kvs : List EtcdKv) (more : Bool) (hst : pfx <+: start) (hl : 0 ≤ sint.Z lim)
    (h : txn.srvRangeOk (pageOp pfx start rev lim) s.kvs kvs more) :
    kvs = (pageKvsL s pfx true start (limN lim)).1 ∧
      txn.srvCount (pageOp pfx start rev lim) s.kvs true =
        W64 ((pageKvsL s pfx true start (limN lim)).2 : Int) := by
  have hR : rangeIn s.kvs (pageOp pfx start rev lim) =
      s.kvs.filter (fun v => kInScope pfx true v.key && !decide (go.GoStringLt v.key start)) := by
    unfold rangeIn
    apply List.filter_congr
    intro v _
    exact inRange_page pfx start v.key hst
  generalize hsc : s.kvs.filter
    (fun v => kInScope pfx true v.key && !decide (go.GoStringLt v.key start)) = sc at hR
  have hpg : pageKvsL s pfx true start (limN lim) =
      (if limN lim = 0 then sc else sc.take (limN lim), sc.length) := by
    unfold pageKvsL; rw [hsc]
  rw [hpg]
  refine ⟨?_, ?_⟩
  · obtain ⟨L, hsort, -, hkvs⟩ := h
    have hord : (pageOp pfx start rev lim).effSortOrder = W64 0 := by
      simp [OpFull.effSortOrder]
    have hL : L = txn.srvPre (pageOp pfx start rev lim) s.kvs := by
      obtain ⟨-, -, -, h4⟩ := hsort
      exact h4 (by rw [hord]; decide) (by rw [hord]; decide)
    have hid : txn.respKv (pageOp pfx start rev lim) = id := by funext v; simp [txn.respKv]
    have hr : txn.kvRead false = id := by funext v; simp [txn.kvRead]
    have hpre : txn.srvPre (pageOp pfx start rev lim) s.kvs =
        mvcc.takeLimit (mvcc.limitOf (txn.rangeLimitOf (pageOp pfx start rev lim))) sc := by
      unfold txn.srvPre
      rw [hR]
      simp [txn.fastKeysOnly, hr]
      try apply List.filter_eq_self.2
      intro v _
      simp [kvFilterOk]
    rw [hkvs, hL, hpre, hid, List.map_id]
    have hlim : (pageOp pfx start rev lim).base.limit = lim := rfl
    unfold txn.srvTrunc txn.srvMore
    rw [hlim]
    have hrl : txn.rangeLimitOf (pageOp pfx start rev lim) =
        (if 0 < sint.Z lim ∧ sint.Z lim < 2 ^ 63 - 1 then lim + W64 1 else lim) := by
      simp [txn.rangeLimitOf, txn.isDefaultOrd, txn.hasRevFilters]
    rw [hrl]
    unfold limN
    by_cases h0 : 0 < sint.Z lim
    · have hn0 : sint.nat lim ≠ 0 := by unfold sint.nat; word
      simp only [h0, ↓reduceIte, hn0, true_and]
      by_cases hmx : sint.Z lim < 2 ^ 63 - 1
      · have hl1 : mvcc.limitOf (lim + W64 1) = some ((sint.Z lim).toNat + 1) := by
          unfold mvcc.limitOf
          have : sint.Z (lim + W64 1) = sint.Z lim + 1 := by word
          rw [this]; simp only [show 0 < sint.Z lim + 1 by omega, ↓reduceIte]; congr 1; omega
        simp only [hmx, ↓reduceIte, hl1, mvcc.takeLimit]
        unfold sint.nat
        by_cases hm : (sint.Z lim) < ((sc.take ((sint.Z lim).toNat + 1)).length : Int)
        · simp only [hm, decide_true, ↓reduceIte, List.take_take]
          congr 1; word
        · simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte]
          simp only [List.length_take] at hm
          rw [List.take_of_length_le (by word), List.take_of_length_le (by word)]
      · have hl1 : mvcc.limitOf lim = some (sint.Z lim).toNat := by
          unfold mvcc.limitOf; simp [h0]
        simp only [hmx, ↓reduceIte, hl1, mvcc.takeLimit]
        unfold sint.nat
        have hm : ¬ (sint.Z lim) < ((sc.take (sint.Z lim).toNat).length : Int) := by
          simp only [List.length_take]; word
        simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte]
    · have hl1 : mvcc.limitOf lim = none := by unfold mvcc.limitOf; simp [h0]
      simp [h0, hl1, mvcc.takeLimit]
  · unfold txn.srvCount
    rw [hR]
    simp [mvcc.totalOf]

end pure

end k8s

end EtcdGrove
end Perennial
