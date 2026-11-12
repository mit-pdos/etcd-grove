/-
**The rebuild's index is the log's** (the restore plan, R3b): for a well-formed log with no
compaction, the index `restoreIntoIndex` rebuilds from the bucket's entries (`idxRestore`, the
code's fold) is the index of the log's events (`indexOf`). A key's first entry is a put, with
version `1` and its own revision as create revision (so `restore` agrees with `put` on a fresh
key index: the model's `created` is the main revision, `Gen`), and a tombstone is never a key's
first entry (`LogWf'`: a delete only of a present key). Lean-first, pure.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvRestore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.SyncModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-- A key the index of a log's prefix does not have is absent from the state there (the
middle of a revision: the first `i` changes of `cs`). -/
theorem findKey_none_of_idxGet_none {log : Log} {cs : List Change}
    (hl : log.length + 1 < 2 ^ 63) (hcs : cs.length < 2 ^ 63)
    (hcsl : ∀ c ∈ log, c.length < 2 ^ 63) (hwf : LogWf' (log ++ [cs])) {i : Nat}
    (hi : i ≤ cs.length) (k : GoString)
    (h : idxGet (indexOf (evsOf log ++ evsOfRev log.length (cs.take i))) k = none) :
    findKey k (applyChanges (W64 log.length) (stateAfter log) (cs.take i)) = none := by
  have hk0 := keyLink_of_rev k log.reverse (by simp; omega)
    (fun c hc => hcsl c (List.mem_reverse.1 hc)) (by rw [List.reverse_reverse]; exact hwf.prefix)
  rw [List.reverse_reverse] at hk0
  have hrs := (rev_step log cs hl hcs hwf k _ hk0 i hi).2.2.2 log.length (Nat.le_refl _) (by omega)
  rw [idxGet_indexOf_eq_none_iff, kiOfKey_eq_kiFold, kiFold_append, ← kiOfKey_eq_kiFold] at h
  rw [h, kiGet_kiEmpty] at hrs
  exact KvMatch_none_left hrs

/-- What a put of a key absent from the state writes: the key created at the revision, version
`1`. -/
theorem changeKv_put_new {r : w64} {b : List EtcdKv} (hb : b.Pairwise etcdKvLess)
    {cs : List Change} {i : Nat} {k v : GoString} {l : w64} (hc : cs[i]? = some (.put k v l))
    (hnew : findKey k (applyChanges r b (cs.take i)) = none) {kv : EtcdKv}
    (hkv : changeKv r b cs i = some kv) :
    kv.key = k ∧ kv.createRev = r ∧ kv.version = W64 0 + W64 1 := by
  unfold changeKv at hkv
  rw [hc] at hkv
  simp only at hkv
  rw [take_succ_getElem cs i _ hc, applyChanges_append_singleton] at hkv
  simp only [applyChange] at hkv
  obtain ⟨nv, hnv, hk, -, hcr, hver⟩ :=
    findKey_putKv_self (applyChanges_sorted r (cs.take i) hb) r k v l
  rw [hnv] at hkv
  cases hkv
  rw [hnew] at hcr hver
  exact ⟨hk, hcr, hver⟩

/-- **One change**: the rebuild's step on the change's bucket entry is the index's step on its
event. -/
theorem idxRestoreEnt_step {log : Log} {cs : List Change}
    (hl : log.length + 1 < 2 ^ 63) (hcs : cs.length < 2 ^ 63)
    (hcsl : ∀ c ∈ log, c.length < 2 ^ 63) (hwf : LogWf' (log ++ [cs])) (hne : log ≠ [])
    {i : Nat} (hi : i < cs.length) {kv : EtcdKv}
    (hkv : changeKv (W64 log.length) (stateAfter log) cs i = some kv) :
    idxRestoreEnt (indexOf (evsOf log ++ evsOfRev log.length (cs.take i)))
        ⟨⟨W64 log.length, W64 i⟩, cs[i].isDel, kv⟩ =
      idxApply (indexOf (evsOf log ++ evsOfRev log.length (cs.take i)))
        { rev := ⟨W64 log.length, W64 i⟩, change := cs[i] } := by
  have hb := stateAfter_sorted log
  have hci : cs[i]? = some cs[i] := List.getElem?_eq_getElem hi
  generalize hc : cs[i] = c at hci ⊢
  unfold idxRestoreEnt idxApply
  cases c with
  | del k =>
    -- a delete: the key is present (`LogWf'`), so the index has it
    have hkvk : kv = zeroKv k := by
      unfold changeKv at hkv; rw [hci] at hkv; exact (Option.some.inj hkv).symm
    subst hkvk
    simp only [Change.isDel, ↓reduceIte, Ev.tomb, Ev.key, Change.key]
    show (match idxGet _ (zeroKv k).key with
      | some ki => if kiLastEmpty ki then _ else _ | none => _) = idxTombstone _ k _
    rw [show (zeroKv k).key = k from rfl]
    unfold idxTombstone
    cases hg : idxGet (indexOf (evsOf log ++ evsOfRev log.length (cs.take i))) k with
    | some ki => rfl
    | none =>
      exfalso
      have hpres := hwf.2 log.length cs i k (by simp) hci
      rw [stateAt_append_lt log cs (by have := List.length_pos_iff.2 hne; omega), stateAt_last] at hpres
      rw [findKey_none_of_idxGet_none hl hcs hcsl hwf (Nat.le_of_lt hi) k hg] at hpres
      cases hpres
  | put k v l =>
    simp only [Change.isDel, Bool.false_eq_true, ↓reduceIte, Ev.tomb, Ev.key, Change.key]
    have hkk : kv.key = k := by
      unfold changeKv at hkv; rw [hci] at hkv; exact findKey_key hkv
    rw [hkk]
    unfold idxPut
    cases hg : idxGet (indexOf (evsOf log ++ evsOfRev log.length (cs.take i))) k with
    | some ki => rfl
    | none =>
      have hnew := findKey_none_of_idxGet_none hl hcs hcsl hwf (Nat.le_of_lt hi) k hg
      obtain ⟨-, hcr, hver⟩ := changeKv_put_new hb hci hnew hkv
      simp only [kiRestore, kiPut, KeyIndex.fresh, genPut, Gen.empty, hcr, hver, ↓reduceIte]
      rfl

/-- Every change of a revision has a bucket entry (`changeKv` is never `none` on a change). -/
theorem changeKv_isSome (r : w64) (b : List EtcdKv) (hb : b.Pairwise etcdKvLess) (cs : List Change)
    {i : Nat} (hi : i < cs.length) : ∃ kv, changeKv r b cs i = some kv := by
  have hci : cs[i]? = some cs[i] := List.getElem?_eq_getElem hi
  unfold changeKv
  rw [hci]
  generalize cs[i] = c at hci ⊢
  cases c with
  | del k => exact ⟨_, rfl⟩
  | put k v l =>
    simp only
    rw [take_succ_getElem cs i _ hci, applyChanges_append_singleton]
    obtain ⟨nv, hnv, -⟩ := findKey_putKv_self (applyChanges_sorted r (cs.take i) hb) r k v l
    exact ⟨nv, hnv⟩

/-- **One revision**: the rebuild over its entries is the index over its events. -/
theorem idxRestore_rev {log : Log} {cs : List Change}
    (hl : log.length + 1 < 2 ^ 63) (hcs : cs.length < 2 ^ 63)
    (hcsl : ∀ c ∈ log, c.length < 2 ^ 63) (hwf : LogWf' (log ++ [cs])) (hne : log ≠ []) :
    ∀ i, i ≤ cs.length →
      ((List.range i).filterMap fun j =>
          (changeKv (W64 log.length) (stateAfter log) cs j).map fun kv =>
            (⟨⟨W64 log.length, W64 j⟩, (cs.getD j (.del [])).isDel, kv⟩ : KvEnt)).foldl
        idxRestoreEnt (indexOf (evsOf log)) =
      indexOf (evsOf log ++ evsOfRev log.length (cs.take i))
  | 0, _ => by simp [evsOfRev]
  | i + 1, hi => by
    have hlt : i < cs.length := by omega
    rw [List.range_succ, List.filterMap_append, List.foldl_append,
      idxRestore_rev hl hcs hcsl hwf hne i (by omega)]
    obtain ⟨kv, hkv⟩ := changeKv_isSome (W64 log.length) (stateAfter log) (stateAfter_sorted log)
      cs hlt
    simp only [List.filterMap_cons, List.filterMap_nil, hkv, Option.map_some]
    rw [List.foldl_cons, List.foldl_nil, show cs.getD i (.del []) = cs[i] by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]]
    rw [idxRestoreEnt_step hl hcs hcsl hwf hne hlt hkv, evsOfRev_take_succ _ _ hlt]
    unfold indexOf
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem logEnts_snoc (log : Log) (cs : List Change) :
    logEnts (log ++ [cs]) 0 (log.length + 1) =
      logEnts log 0 log.length ++ entsOfRev log.length (stateAt (log ++ [cs]) (log.length - 1)) cs := by
  unfold logEnts
  simp only [Nat.sub_zero]
  rw [List.range'_1_concat, List.map_append, List.flatten_append]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro m hm
    rw [List.mem_range'_1] at hm
    have hm' : m < log.length := by omega
    rw [stateAt_append_lt log cs (by omega)]
    congr 1
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hm']
  · simp [List.getD_eq_getElem?_getD]

/-- **The rebuild's index is the log's.** -/
theorem idxRestore_logEnts : ∀ (rl : List (List Change)), rl.length < 2 ^ 63 →
    (∀ cs ∈ rl, cs.length < 2 ^ 63) → LogWf' rl.reverse →
    idxRestore (logEnts rl.reverse 0 rl.reverse.length) = indexOf (evsOf rl.reverse)
  | [], _, _, _ => by simp [logEnts, idxRestore, indexOf, evsOf]
  | cs :: rl, hlen, hcs, hwf => by
    rw [List.reverse_cons] at hwf ⊢
    have hl : rl.reverse.length + 1 < 2 ^ 63 := by simp at hlen ⊢; omega
    have hcs1 : cs.length < 2 ^ 63 := hcs cs List.mem_cons_self
    have hcsl : ∀ c ∈ rl.reverse, c.length < 2 ^ 63 :=
      fun c hc => hcs c (List.mem_cons_of_mem _ (List.mem_reverse.1 hc))
    have ih := idxRestore_logEnts rl (by simp at hlen; omega)
      (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) hwf.prefix
    rw [List.length_append, List.length_singleton, logEnts_snoc, evsOf_append]
    unfold idxRestore at ih ⊢
    rw [List.foldl_append, ih]
    by_cases hne : rl.reverse = []
    · -- the first revision: no change (`LogWf'`)
      have hnil : cs = [] := by
        have h0 := hwf.1 (by simp)
        rw [hne] at h0
        simpa using h0
      subst hnil
      simp [entsOfRev, evsOfRev, indexOf]
    · rw [stateAt_append_lt _ cs (by have := List.length_pos_iff.2 hne; omega), stateAt_last,
        entsOfRev_range]
      have h := idxRestore_rev hl hcs1 hcsl hwf hne cs.length (Nat.le_refl _)
      rw [List.take_length] at h
      rw [h]
      try (unfold indexOf; rw [List.foldl_append])

/-- `idxRestore_logEnts` for a log. -/
theorem idxRestore_logEnts' (log : Log) (hlen : log.length < 2 ^ 63)
    (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) (hwf : LogWf' log) :
    idxRestore (logEnts log 0 log.length) = indexOf (evsOf log) := by
  have := idxRestore_logEnts log.reverse (by simpa using hlen)
    (fun c hc => hcs c (List.mem_reverse.1 hc)) (by rw [List.reverse_reverse]; exact hwf)
  rwa [List.reverse_reverse] at this

end mvcc
end EtcdGrove
end Perennial
