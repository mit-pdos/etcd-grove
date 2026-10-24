/-
**`restore`'s chunk loop over a log's bucket** (the restore plan's R5c): the `Key` bucket of a
well-formed log `L` holds the entries `logEnts L 0 |L|` (`bucketOf_logEnts`), sorted by revision;
the range from a revision's bytes to `{MaxInt64, MaxInt64}`'s is the entries from that revision
on, and the next chunk starts just after the last entry of a full one. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreModel
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketRange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RevBytes
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-- Revisions as pairs of naturals, ordered lexicographically (the bucket's key order). -/
def revLeN (r e : Rev) : Prop :=
  r.main.toNat < e.main.toNat ∨ (r.main = e.main ∧ r.sub.toNat ≤ e.sub.toNat)

instance revLeN_dec : DecidableRel revLeN := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- A revision's key (no tombstone mark) is at most an entry's key iff the revision is at most
the entry's. -/
theorem revBytes_le_iff (r e : Rev) (t : Bool) :
    go.GoStringLe (revBytes r false) (revBytes e t) ↔ revLeN r e := by
  constructor
  · intro h
    unfold revLeN
    rcases Nat.lt_or_ge r.main.toNat e.main.toNat with hm | hm
    · exact Or.inl hm
    rcases Nat.lt_or_ge e.main.toNat r.main.toNat with hm' | hm'
    · exact absurd h (goStringLe_of_lt_not (revBytes_lt_main e r t false hm'))
    have hme : r.main = e.main := BitVec.eq_of_toNat_eq (by omega)
    refine Or.inr ⟨hme, ?_⟩
    rcases Nat.lt_or_ge e.sub.toNat r.sub.toNat with hs | hs
    · exact absurd h (goStringLe_of_lt_not (revBytes_lt_sub e r t false hme.symm hs))
    · exact hs
  · rintro (hm | ⟨hme, hs⟩)
    · exact Or.inr (revBytes_lt_main r e false t hm)
    · rcases Nat.lt_or_ge r.sub.toNat e.sub.toNat with hs' | hs'
      · exact Or.inr (revBytes_lt_sub r e false t hme hs')
      · have hse : r.sub = e.sub := by apply BitVec.eq_of_toNat_eq; omega
        have hre : r = e := by cases r; cases e; simp_all
        subst hre
        cases t
        · exact Or.inl rfl
        · rw [revBytes_true]
          exact Or.inr (by simpa using lex_prefix (revBytes r false) markTomb [])

/-- An entry's key is below a revision's key iff the entry's revision is below it. -/
theorem revBytes_lt_iff (r e : Rev) (t : Bool) :
    go.GoStringLt (revBytes e t) (revBytes r false) ↔ ¬ revLeN r e := by
  rw [← revBytes_le_iff r e t]
  constructor
  · exact fun h => goStringLe_of_lt_not h
  · intro h
    rcases goStringLe_total (revBytes r false) (revBytes e t) with h' | h'
    · exact absurd h' h
    · rcases h' with h' | h'
      · exact absurd (Or.inl h'.symm) h
      · exact h'

/-- `{MaxInt64, MaxInt64}`, `restore`'s range's end. -/
def revMax : Rev := ⟨W64 (2 ^ 63 - 1), W64 (2 ^ 63 - 1)⟩

/-- The entries of a log from the revision `r` on. -/
def entsFrom (log : Log) (r : Rev) : List KvEnt :=
  (logEnts log 0 log.length).filter fun e => decide (revLeN r e.rev)

/-- An entry of a log's bucket is below `revMax`'s key. -/
theorem logEnts_lt_max (log : Log) (hlen : log.length < 2 ^ 63) (e : KvEnt)
    (he : e ∈ logEnts log 0 log.length) :
    go.GoStringLt (revBytes e.rev e.tomb) (revBytes revMax false) := by
  obtain ⟨j, i, c, kv, -, -, hj, -, -, -, -, rfl⟩ := logEnts_entry log 0 log.length e he
  apply revBytes_lt_main
  show (W64 j).toNat < (W64 (2 ^ 63 - 1)).toNat
  rw [w64_toNat_of_lt j (by omega),
    show (W64 (2 ^ 63 - 1)).toNat = 2 ^ 63 - 1 from w64_toNat_of_lt (2 ^ 63 - 1) (by omega)]
  omega

/-- **The range `restore` reads from the revision `r`** (to `revMax`) of a well-formed log's
bucket: the log's entries from `r` on, in revision order. -/
theorem bucketRange_from (log : Log) (hlen : log.length < 2 ^ 63)
    (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) (r : Rev) :
    bucketRange (bucketMap log) (revBytes r false) (revBytes revMax false) =
      (entsFrom log r).map KvEnt.pair := by
  rw [bucketRange_eq_iff]
  constructor
  · rw [List.map_map, List.pairwise_map]
    exact (logEnts_keys_sorted log hlen hcs 0 log.length).sublist List.filter_sublist
  · intro k v
    rw [bucketMap_lookup_iff log hlen hcs, bucketOf_logEnts]
    simp only [entsFrom, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨e, ⟨he, hr⟩, hpe⟩
      simp only [KvEnt.pair, Prod.mk.injEq] at hpe
      obtain ⟨rfl, rfl⟩ := hpe
      exact ⟨⟨e, he, rfl⟩, (revBytes_le_iff r e.rev e.tomb).2 hr, logEnts_lt_max log hlen e he⟩
    · rintro ⟨⟨e, he, hpe⟩, hk1, -⟩
      simp only [KvEnt.pair, Prod.mk.injEq] at hpe
      obtain ⟨rfl, rfl⟩ := hpe
      exact ⟨e, ⟨he, (revBytes_le_iff r e.rev e.tomb).1 hk1⟩, rfl⟩

/-- A revision as a natural number, in the bucket's key order. -/
def revCode (r : Rev) : Nat := r.main.toNat * 2 ^ 64 + r.sub.toNat

theorem revLeN_iff (r e : Rev) : revLeN r e ↔ revCode r ≤ revCode e := by
  unfold revLeN revCode
  have h1 := r.sub.isLt
  have h2 := e.sub.isLt
  constructor
  · rintro (h | ⟨h, h'⟩)
    · have : r.main.toNat + 1 ≤ e.main.toNat := h
      have := Nat.mul_le_mul_right (2 ^ 64) this
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    · rw [h]; omega
  · intro h
    rcases Nat.lt_or_ge r.main.toNat e.main.toNat with hm | hm
    · exact Or.inl hm
    rcases Nat.lt_or_ge e.main.toNat r.main.toNat with hm' | hm'
    · have : e.main.toNat + 1 ≤ r.main.toNat := hm'
      have := Nat.mul_le_mul_right (2 ^ 64) this
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    have hme : r.main = e.main := BitVec.eq_of_toNat_eq (by omega)
    refine Or.inr ⟨hme, ?_⟩
    rw [hme] at h
    omega

/-- **The entries of a log are sorted by revision.** -/
theorem logEnts_codes_sorted (log : Log) (hlen : log.length < 2 ^ 63)
    (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) (lo hi : Nat) :
    (logEnts log lo hi).Pairwise (fun e e' => revCode e.rev < revCode e'.rev) := by
  unfold logEnts
  rw [List.pairwise_flatten, List.pairwise_map]
  constructor
  · intro l hl
    rw [List.mem_map] at hl
    obtain ⟨j, -, rfl⟩ := hl
    rw [entsOfRev_range]
    apply List.Pairwise.filterMap (R := (· < ·)) _ _ List.pairwise_lt_range
    intro i i' hii e he e' he'
    have hb := getD_len_bound log hcs j
    cases hk : changeKv (W64 j) (stateAt log (j - 1)) (log.getD j []) i' with
    | none => rw [hk] at he'; cases he'
    | some kv' =>
      have hi' : i' < (log.getD j []).length := by
        unfold changeKv at hk
        cases hc : (log.getD j [])[i']? with
        | none => rw [hc] at hk; cases hk
        | some _ => exact (List.getElem?_eq_some_iff.1 hc).1
      cases hk0 : changeKv (W64 j) (stateAt log (j - 1)) (log.getD j []) i with
      | none => rw [hk0] at he; cases he
      | some kv =>
        rw [hk0] at he; rw [hk] at he'
        simp only [Option.map_some, Option.some.injEq] at he he'
        subst he; subst he'
        unfold revCode
        simp only
        rw [w64_toNat_of_lt i (by omega), w64_toNat_of_lt i' (by omega)]
        omega
  · apply (List.pairwise_lt_range' (s := lo) (n := hi - lo)).imp_of_mem
    intro j j' _ _ hjj x hx y hy
    have hx' := entsOfRev_main log j x hx
    have hy' := entsOfRev_main log j' y hy
    have hxs := x.rev.sub.isLt
    unfold revCode
    rw [hx'.2, hy'.2, w64_toNat_of_lt j (by omega), w64_toNat_of_lt j' (by omega)]
    have : j + 1 ≤ j' := hjj
    have := Nat.mul_le_mul_right (2 ^ 64) this
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

/-- In a list sorted by `f`, what follows the first `n` is what is above its `n`-th. -/
theorem drop_eq_filter_gt {α : Type} (f : α → Nat) {l : List α}
    (hs : l.Pairwise (fun a b => f a < f b)) (n : Nat) (hn : 0 < n) (e : α)
    (he : l[n - 1]? = some e) :
    l.drop n = l.filter (fun x => decide (f e < f x)) := by
  have hlt : n - 1 < l.length := (List.getElem?_eq_some_iff.1 he).1
  have hsplit : l = l.take (n - 1) ++ ([e] ++ l.drop n) := by
    conv => lhs; rw [← List.take_append_drop (n - 1) l]
    congr 1
    rw [List.drop_eq_getElem_cons hlt]
    have : l[n - 1] = e := (List.getElem?_eq_some_iff.1 he).2
    rw [this, show n - 1 + 1 = n by omega]
    rfl
  have hs' := hs
  rw [hsplit] at hs'
  rw [List.pairwise_append, List.pairwise_append] at hs'
  obtain ⟨-, ⟨-, -, hmid⟩, hcross⟩ := hs'
  conv => rhs; rw [hsplit]
  rw [List.filter_append, List.filter_append]
  have h1 : (l.take (n - 1)).filter (fun x => decide (f e < f x)) = [] := by
    apply List.filter_eq_nil_iff.2
    intro a ha
    have := hcross a ha e (by simp)
    simp only [decide_eq_true_eq]; omega
  have h2 : [e].filter (fun x => decide (f e < f x)) = [] := by simp
  have h3 : (l.drop n).filter (fun x => decide (f e < f x)) = l.drop n := by
    apply List.filter_eq_self.2
    intro b hb
    have := hmid e (by simp) b hb
    simpa using this
  rw [h1, h2, h3]; rfl

/-- The revision just after `r` (`newMin.Sub++`). -/
def revNext (r : Rev) : Rev := ⟨r.main, r.sub + W64 1⟩

theorem revCode_next (r : Rev) (h : r.sub.toNat + 1 < 2 ^ 64) :
    revCode (revNext r) = revCode r + 1 := by
  unfold revCode revNext
  simp only
  have : (r.sub + W64 1).toNat = r.sub.toNat + 1 := by
    rw [BitVec.toNat_add]
    simp only [show (W64 1).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt h
  omega

/-- An entry's sub-revision leaves room for `Sub++`. -/
theorem logEnts_sub_lt (log : Log) (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) (e : KvEnt)
    (he : e ∈ logEnts log 0 log.length) : e.rev.sub.toNat + 1 < 2 ^ 64 := by
  obtain ⟨j, i, c, kv, -, -, hj, hgj, -, hc, -, rfl⟩ := logEnts_entry log 0 log.length e he
  have hcl := hcs _ (List.mem_of_getElem? hgj)
  have hil : i < (log.getD j []).length := (List.getElem?_eq_some_iff.1 hc).1
  have hb := getD_len_bound log hcs j
  show (W64 i).toNat + 1 < 2 ^ 64
  rw [w64_toNat_of_lt i (by omega)]
  omega

/-- **The next chunk** (R5c): after a full chunk of `n` entries from `r`, whose last is `e`, the
entries from just after `e` are the rest. -/
theorem entsFrom_next (log : Log) (hlen : log.length < 2 ^ 63)
    (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) (r : Rev) (n : Nat) (hn : 0 < n) (e : KvEnt)
    (he : (entsFrom log r)[n - 1]? = some e) :
    entsFrom log (revNext e.rev) = (entsFrom log r).drop n := by
  have hsE := logEnts_codes_sorted log hlen hcs 0 log.length
  have hsR : (entsFrom log r).Pairwise (fun a b => revCode a.rev < revCode b.rev) :=
    hsE.sublist List.filter_sublist
  rw [drop_eq_filter_gt (fun e : KvEnt => revCode e.rev) hsR n hn e he]
  have hmem : e ∈ entsFrom log r := List.mem_of_getElem? he
  have heE : e ∈ logEnts log 0 log.length := (List.mem_filter.1 hmem).1
  have her : revLeN r e.rev := by simpa using (List.mem_filter.1 hmem).2
  rw [revLeN_iff] at her
  have hc := revCode_next e.rev (logEnts_sub_lt log hcs e heE)
  unfold entsFrom
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  simp only [revLeN_iff]
  rw [hc]
  by_cases h1 : revCode r ≤ revCode x.rev <;> by_cases h2 : revCode e.rev < revCode x.rev <;>
    simp [h1, h2] <;> omega

/-- **A log's entries are what `restoreIntoIndex` takes** (`RestoreEntsOk`): sorted by revision,
none at revision `0` (the log's first revision is empty). -/
theorem logEnts_restoreOk (log : Log) (hlen : log.length < 2 ^ 63)
    (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) (h0 : log.getD 0 [] = []) :
    RestoreEntsOk (logEnts log 0 log.length) := by
  have hb : ∀ e ∈ logEnts log 0 log.length, ∃ j i : Nat, 1 ≤ j ∧ j < log.length ∧
      i < 2 ^ 63 ∧ e.rev = ⟨W64 j, W64 i⟩ := by
    intro e he
    obtain ⟨j, i, c, kv, -, -, hj, hgj, -, hc, -, rfl⟩ := logEnts_entry log 0 log.length e he
    have hcl := hcs _ (List.mem_of_getElem? hgj)
    have hil : i < (log.getD j []).length := (List.getElem?_eq_some_iff.1 hc).1
    have hb := getD_len_bound log hcs j
    refine ⟨j, i, ?_, hj, by omega, rfl⟩
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [h0] at hil; simp at hil
    · exact hpos
  constructor
  · apply (logEnts_codes_sorted log hlen hcs 0 log.length).imp_of_mem
    intro a b ha hb' hab
    obtain ⟨j, i, -, hj, hi, hra⟩ := hb a ha
    obtain ⟨j', i', -, hj', hi', hrb⟩ := hb b hb'
    unfold revCode at hab
    rw [hra, hrb] at hab ⊢
    simp only at hab
    rw [w64_toNat_of_lt j (by omega), w64_toNat_of_lt i (by omega),
      w64_toNat_of_lt j' (by omega), w64_toNat_of_lt i' (by omega)] at hab
    unfold Rev.lt
    simp only
    rcases Nat.lt_or_ge j j' with hjj | hjj
    · left; word
    · have : j = j' := by
        rcases Nat.lt_or_ge j' j with h | h
        · have : j' + 1 ≤ j := h
          have := Nat.mul_le_mul_right (2 ^ 64) this
          rw [Nat.add_mul, Nat.one_mul] at this
          omega
        · omega
      subst this
      right; exact ⟨rfl, by word⟩
  · intro e he
    obtain ⟨j, i, h1, hj, hi, hr⟩ := hb e he
    rw [hr]
    constructor <;> word

/-- A log's index with a revision of changes `pend` so far is its compacted form at `-1`. -/
theorem idxCRep_indexOf_pend (ilog : Log) (pend : List Change)
    (hb : LogB (ilog ++ [pend])) (h : IdxCRep (-1) (evsOf ilog) (indexOf (evsOf ilog))) :
    IdxCRep (-1) (evsOf (ilog ++ [pend])) (indexOf (evsOf (ilog ++ [pend]))) := by
  obtain ⟨n, hn⟩ : ∃ n, pend.length = n := ⟨_, rfl⟩
  induction n generalizing pend with
  | zero =>
    have : pend = [] := List.eq_nil_of_length_eq_zero hn
    subst this
    rw [evsOf_append]
    simpa [evsOfRev] using h
  | succ n ih =>
    have hne : pend ≠ [] := by intro h'; simp [h'] at hn
    rw [← List.dropLast_concat_getLast hne] at hb ⊢
    have hb' : LogB (ilog ++ [pend.dropLast]) := by
      refine ⟨by simpa using hb.1, ?_⟩
      intro cs hcs
      rcases List.mem_append.1 hcs with h1 | h1
      · exact hb.2 cs (List.mem_append_left _ h1)
      · rw [List.mem_singleton] at h1; subst h1
        have := hb.2 (pend.dropLast ++ [pend.getLast hne]) (by simp)
        simp at this; simp; omega
    have hl : pend.dropLast.length = n := by simp [hn]
    have := IdxCRep.step ilog pend.dropLast (pend.getLast hne) hb (cmax := -1) (by omega)
      (ih pend.dropLast hb' hl)
    rw [evsOf_append_change]
    unfold indexOf at this ⊢
    rw [List.foldl_append]
    rw [evsOf_append_change] at this
    exact this

/-- **A log's index is its own compacted form at `-1`** (no compaction). -/
theorem idxCRep_indexOf (log : Log) (hb : LogB log) :
    IdxCRep (-1) (evsOf log) (indexOf (evsOf log)) := by
  obtain ⟨n, hn⟩ : ∃ n, log.length = n := ⟨_, rfl⟩
  induction n generalizing log with
  | zero =>
    have : log = [] := List.eq_nil_of_length_eq_zero hn
    subst this
    exact IdxCRep.nil (by omega)
  | succ n ih =>
    have hne : log ≠ [] := by intro h'; simp [h'] at hn
    rw [← List.dropLast_concat_getLast hne] at hb ⊢
    have hl : log.dropLast.length = n := by simp [hn]
    exact idxCRep_indexOf_pend log.dropLast (log.getLast hne) hb (ih log.dropLast hb.prefix hl)

/-- A revision with changes has an entry. -/
theorem entsOfRev_ne_nil (r : Nat) (b : List EtcdKv) (hb : b.Pairwise etcdKvLess)
    (cs : List Change) (hne : cs ≠ []) : entsOfRev r b cs ≠ [] := by
  have h0 : 0 < cs.length := List.length_pos_iff.2 hne
  obtain ⟨kv, hkv⟩ := changeKv_isSome (W64 r) b hb cs h0
  intro h
  have hc : cs[0]? = some cs[0] := List.getElem?_eq_getElem h0
  have hm := (mem_entsOfRev r b cs ⟨⟨W64 r, W64 0⟩, cs[0].isDel, kv⟩).2 ⟨0, cs[0], kv, hc, hkv, rfl⟩
  rw [h] at hm
  simp at hm

/-- **The last revision `restoreIntoIndex` answers** for a restored log `[[], []] ++ R` whose
revisions all have changes: its last revision. -/
theorem restoreLastRev_logEnts (R : Log) (hR : ∀ cs ∈ R, cs ≠ []) (hlen : R.length + 2 < 2 ^ 63) :
    restoreLastRev (logEnts ([[], []] ++ R) 0 ([[], []] ++ R).length) =
      W64 ((([[], []] ++ R).length : Int) - 1) := by
  rcases List.eq_nil_or_concat R with rfl | ⟨R0, cs, rfl⟩
  · decide
  · simp only [List.concat_eq_append] at hR hlen ⊢
    have hcs : cs ≠ [] := hR cs (by simp)
    have hsnoc := logEnts_snoc ([[], []] ++ R0) cs
    have hl : ([[], []] ++ R0 ++ [cs]).length = ([[], []] ++ R0).length + 1 := by simp
    rw [← List.append_assoc, hl, hsnoc]
    have hB := entsOfRev_ne_nil ([[], []] ++ R0).length
      (stateAt (([[], []] ++ R0) ++ [cs]) (([[], []] ++ R0).length - 1))
      (stateAt_sorted _ _) cs hcs
    unfold restoreLastRev
    obtain ⟨e, he⟩ : ∃ e, (entsOfRev ([[], []] ++ R0).length
        (stateAt (([[], []] ++ R0) ++ [cs]) (([[], []] ++ R0).length - 1)) cs).getLast? = some e :=
      Option.isSome_iff_exists.1 (by
        rw [List.getLast?_isSome]; exact hB)
    rw [List.getLast?_append, he]
    simp only [Option.some_or]
    have hem := List.mem_of_getLast? he
    obtain ⟨i, c, kv, -, -, rfl⟩ := (mem_entsOfRev _ _ _ _).1 hem
    simp only [List.length_append, List.length_cons, List.length_nil]
    congr 1
    push_cast
    omega

/-- Every key-value of a state has lease `0`. -/
def LeaseZero (s : List EtcdKv) : Prop := ∀ kv ∈ s, kv.lease = W64 0

/-- A log's puts carry no lease. -/
def LogNoLease (log : Log) : Prop :=
  ∀ cs ∈ log, ∀ c ∈ cs, ∀ (k v : GoString) (l : w64), c = .put k v l → l = W64 0

theorem LeaseZero.applyChange {s : List EtcdKv} (hs : LeaseZero s) (r : w64) (c : Change)
    (hc : ∀ (k v : GoString) (l : w64), c = .put k v l → l = W64 0) :
    LeaseZero (applyChange r s c) := by
  cases c with
  | put k v l =>
    have hl := hc k v l rfl
    subst hl
    intro kv hkv
    simp only [mvcc.applyChange, putKv] at hkv
    rcases btInsert_mem hkv with rfl | h
    · split <;> rfl
    · exact hs kv h
  | del k =>
    intro kv hkv
    exact hs kv (List.mem_filter.1 hkv).1

theorem LeaseZero.applyChanges {s : List EtcdKv} (hs : LeaseZero s) (r : w64) (cs : List Change)
    (hc : ∀ c ∈ cs, ∀ (k v : GoString) (l : w64), c = .put k v l → l = W64 0) :
    LeaseZero (mvcc.applyChanges r s cs) := by
  induction cs generalizing s with
  | nil => exact hs
  | cons c cs ih =>
    unfold mvcc.applyChanges
    rw [List.foldl_cons]
    exact ih (hs.applyChange r c (hc c (by simp))) (fun c' h => hc c' (by simp [h]))

theorem stateAfter_leaseZero (log : Log) (h : LogNoLease log) : LeaseZero (stateAfter log) := by
  unfold stateAfter
  have : ∀ (l : List (List Change × Nat)) (s : List EtcdKv), LeaseZero s →
      (∀ p ∈ l, ∀ c ∈ p.1, ∀ (k v : GoString) (l : w64), c = .put k v l → l = W64 0) →
      LeaseZero (l.foldl (fun s p => mvcc.applyChanges (W64 p.2) s p.1) s) := by
    intro l
    induction l with
    | nil => intro s hs _; exact hs
    | cons p l ih =>
      intro s hs hl
      rw [List.foldl_cons]
      exact ih _ (hs.applyChanges _ _ (hl p (by simp))) (fun p' hp => hl p' (by simp [hp]))
  apply this _ [] (fun _ h => by cases h)
  intro p hp
  exact h p.1 (List.fst_mem_of_mem_zipIdx hp)

theorem stateAt_leaseZero (log : Log) (h : LogNoLease log) (r : Nat) :
    LeaseZero (stateAt log r) :=
  stateAfter_leaseZero _ (fun cs hcs => h cs (List.mem_of_mem_take hcs))

/-- **No entry of a log without leases has one** (what `restoreChunk` takes: `keyToLease`
stays empty). -/
theorem logEnts_lease (log : Log) (h : LogNoLease log) (lo hi : Nat) :
    ∀ e ∈ logEnts log lo hi, e.kv.lease = W64 0 := by
  intro e he
  obtain ⟨j, -, -, he'⟩ := (mem_logEnts log lo hi e).1 he
  obtain ⟨i, c, kv, hc, hkv, rfl⟩ := (mem_entsOfRev _ _ _ _).1 he'
  simp only
  have hcs : ∀ c ∈ log.getD j [], ∀ (k v : GoString) (l : w64), c = .put k v l → l = W64 0 := by
    intro c hc k v l hcl
    rw [List.getD_eq_getElem?_getD] at hc
    cases hg : log[j]? with
    | none => rw [hg] at hc; simp at hc
    | some cs => rw [hg] at hc; exact h cs (List.mem_of_getElem? hg) c hc k v l hcl
  unfold changeKv at hkv
  rw [hc] at hkv
  cases c with
  | put k v l =>
    simp only at hkv
    exact (stateAt_leaseZero log h _).applyChanges _ _
      (fun c' hc' => hcs c' (List.mem_of_mem_take hc')) kv (findKey_mem hkv)
  | del k =>
    simp only [Option.some.injEq] at hkv
    subst hkv; rfl

theorem sub_succ_nonneg (x : w64) (h : x.toNat < 2 ^ 63 - 1) : 0 ≤ sint.Z (x + W64 1) := by
  word

end mvcc
end EtcdGrove
end Perennial
