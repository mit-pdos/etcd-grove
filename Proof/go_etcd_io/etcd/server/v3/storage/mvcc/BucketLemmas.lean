/-
The bucket's entries of the answers of a range read: every answer `(key, (mod, created, ver))`
of `rangeAnswers` at a revision `r` of a well-formed log is the state's key-value of `key` at
`r` (`kiGet_indexOf`), and the bucket holds that key-value, encoded, at the bytes of `mod`
(`BucketHas`, `bucketMap`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LogLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Hist
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RevBytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ## Words -/

theorem W64_toNat (x : w64) : W64 (x.toNat : Int) = x := by
  first
  | (simp [W64])
  | (unfold W64; simp)
  | (apply BitVec.eq_of_toNat_eq; simp [W64])

theorem W64_inj_of_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : W64 a = W64 b) :
    a = b := by
  first
  | (unfold W64 at h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_ofInt] at this; omega)
  | (have := congrArg BitVec.toNat h; simp [W64] at this; omega)

/-! ## The map built from the bucket's entries -/

/-- The lookup after inserting the entries of `l` (the last one of a key wins). -/
theorem lookup_foldl_insert (l : List (GoString × GoString)) (m : GMap GoString GoString)
    (k : GoString) :
    (l.foldl (fun m p => GMap.insert p.1 p.2 m) m).lookup k =
      match l.reverse.find? (fun p => decide (p.1 = k)) with
      | some p => some p.2
      | none => m.lookup k := by
  induction l generalizing m with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldl_cons, ih, List.reverse_cons, List.find?_append]
    cases h : l.reverse.find? (fun q => decide (q.1 = k)) with
    | some q => simp [Option.or]
    | none =>
      simp only [Option.none_or, List.find?_cons, List.find?_nil]
      by_cases hk : p.1 = k
      · simp only [hk, decide_true]
        rw [← hk, GMap.lookup_insert]
      · simp only [hk, decide_false]
        exact GMap.lookup_insert_ne _ _ hk

/-- The lookup of a key of `bucketOf log` whose entries all hold `v`. -/
theorem bucketMap_lookup_of_mem (log : Log) (key v : GoString) (hmem : (key, v) ∈ bucketOf log)
    (hfun : ∀ p ∈ bucketOf log, p.1 = key → p.2 = v) : (bucketMap log).lookup key = some v := by
  unfold bucketMap
  rw [lookup_foldl_insert]
  cases h : (bucketOf log).reverse.find? (fun p => decide (p.1 = key)) with
  | none =>
    exfalso
    rw [List.find?_eq_none] at h
    exact h (key, v) (List.mem_reverse.2 hmem) (by simp)
  | some p =>
    have hp := List.mem_reverse.1 (List.mem_of_find?_eq_some h)
    have hk : p.1 = key := by simpa using List.find?_some h
    simp only [hfun p hp hk]

/-! ## The encoding is injective -/

theorem revBytes_inj (a b : Rev) (ta tb : Bool) (h : revBytes a ta = revBytes b tb) :
    ta = tb ∧ a = b := by
  have hl := congrArg List.length h
  rw [revBytes_length, revBytes_length] at hl
  have htb : ta = tb := by cases ta <;> cases tb <;> simp at hl ⊢
  subst htb
  refine ⟨rfl, ?_⟩
  have h8 : u64Be a.main = u64Be b.main := by
    have := congrArg (List.take 8) h
    cases ta
    · rwa [revBytes_take8, revBytes_take8] at this
    · rw [revBytes_true, revBytes_true, List.take_append_of_le_length (by simp [revBytes_false_length]),
        List.take_append_of_le_length (by simp [revBytes_false_length]), revBytes_take8,
        revBytes_take8] at this
      exact this
  have h9 : u64Be a.sub = u64Be b.sub := by
    have := congrArg (fun l => (List.drop 9 l).take 8) h
    cases ta
    · simp only [revBytes_drop9] at this
      rwa [List.take_of_length_le (by simp [u64Be_length]),
        List.take_of_length_le (by simp [u64Be_length])] at this
    · simp only [revBytes_true] at this
      rw [List.drop_append_of_le_length (by simp [revBytes_false_length]),
        List.drop_append_of_le_length (by simp [revBytes_false_length]), revBytes_drop9,
        revBytes_drop9, List.take_append_of_le_length (by simp [u64Be_length]),
        List.take_append_of_le_length (by simp [u64Be_length]),
        List.take_of_length_le (by simp [u64Be_length]),
        List.take_of_length_le (by simp [u64Be_length])] at this
      exact this
  have hm : a.main = b.main := by
    have := congrArg beToU64 h8; rwa [beToU64_u64Be, beToU64_u64Be] at this
  have hs : a.sub = b.sub := by
    have := congrArg beToU64 h9; rwa [beToU64_u64Be, beToU64_u64Be] at this
  cases a; cases b; simp only at hm hs; rw [hm, hs]

/-! ## The bucket's entry of a change -/

/-- The entry of a change (`BucketHas`) is in `bucketOf log`: at the bytes of its revision,
not a tombstone when its key-value's mod revision is the change's (a delete writes
`zeroKv`, mod revision `0`, and revision `0` has no change). -/
theorem bucketOf_mem_of_BucketHas (log : Log) (hwf : LogWf log) (rev : Rev) (kv : EtcdKv)
    (h : BucketHas log rev kv) (hmod : kv.modRev = rev.main) :
    (revBytes rev false, kvEncode kv) ∈ bucketOf log := by
  obtain ⟨cs, hcs, hch⟩ := h
  -- the change is a put
  have hidx : ∃ c, cs[rev.sub.toNat]? = some c := by
    unfold changeKv at hch
    cases hc : cs[rev.sub.toNat]? with
    | none => rw [hc] at hch; simp at hch
    | some c => exact ⟨c, rfl⟩
  obtain ⟨c, hc⟩ := hidx
  have hput : c.isDel = false := by
    cases c with
    | put k v l => rfl
    | del k =>
      exfalso
      unfold changeKv at hch
      rw [hc] at hch
      simp only [Option.some.injEq] at hch
      subst hch
      -- `zeroKv`'s mod revision is 0: revision 0 has no changes
      have h0 : rev.main = W64 0 := by simpa [zeroKv] using hmod.symm
      have hr0 : rev.main.toNat = 0 := by rw [h0]; rfl
      rw [hr0, hwf.1] at hcs
      simp only [Option.some.injEq] at hcs
      subst hcs
      simp at hc
  unfold bucketOf
  rw [List.mem_flatten]
  refine ⟨bucketOfRev rev.main.toNat (stateAt log (rev.main.toNat - 1)) cs, ?_, ?_⟩
  · rw [List.mem_map]
    exact ⟨(cs, rev.main.toNat), List.mem_zipIdx_iff_getElem?.2 hcs, rfl⟩
  · unfold bucketOfRev
    rw [List.mem_filterMap]
    refine ⟨(c, rev.sub.toNat), List.mem_zipIdx_iff_getElem?.2 hc, ?_⟩
    simp only [W64_toNat, hch, Option.map_some, hput]

/-- Two entries of `bucketOf log` at the same bytes are the same entry (the revisions are
below `2 ^ 63`). -/
theorem bucketOf_fun (log : Log) (hlen : log.length < 2 ^ 63)
    (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) :
    ∀ p ∈ bucketOf log, ∀ q ∈ bucketOf log, p.1 = q.1 → p.2 = q.2 := by
  intro p hp q hq hpq
  unfold bucketOf at hp hq
  rw [List.mem_flatten] at hp hq
  obtain ⟨lp, hlp, hp⟩ := hp
  obtain ⟨lq, hlq, hq⟩ := hq
  rw [List.mem_map] at hlp hlq
  obtain ⟨⟨csp, rp⟩, hzp, rfl⟩ := hlp
  obtain ⟨⟨csq, rq⟩, hzq, rfl⟩ := hlq
  rw [List.mem_zipIdx_iff_getElem?] at hzp hzq
  simp only at hzp hzq
  unfold bucketOfRev at hp hq
  rw [List.mem_filterMap] at hp hq
  obtain ⟨⟨cp, ip⟩, hip, hp⟩ := hp
  obtain ⟨⟨cq, iq⟩, hiq, hq⟩ := hq
  rw [List.mem_zipIdx_iff_getElem?] at hip hiq
  simp only at hip hiq
  cases hcp : changeKv (W64 rp) (stateAt log (rp - 1)) csp ip with
  | none => rw [hcp] at hp; simp at hp
  | some kvp =>
  cases hcq : changeKv (W64 rq) (stateAt log (rq - 1)) csq iq with
  | none => rw [hcq] at hq; simp at hq
  | some kvq =>
  rw [hcp] at hp; rw [hcq] at hq
  simp only [Option.map_some, Option.some.injEq] at hp hq
  subst hp; subst hq
  simp only at hpq ⊢
  obtain ⟨-, hrev⟩ := revBytes_inj _ _ _ _ hpq
  simp only [Rev.mk.injEq] at hrev
  have hrp : rp < log.length := (List.getElem?_eq_some_iff.1 hzp).1
  have hrq : rq < log.length := (List.getElem?_eq_some_iff.1 hzq).1
  have hr : rp = rq := W64_inj_of_lt (by omega) (by omega) hrev.1
  subst hr
  have hcseq : csp = csq := by rw [hzp] at hzq; exact Option.some.inj hzq
  subst hcseq
  have hip' : ip < csp.length := (List.getElem?_eq_some_iff.1 hip).1
  have hiq' : iq < csp.length := (List.getElem?_eq_some_iff.1 hiq).1
  have hcsl := hcs csp (List.mem_of_getElem? hzp)
  have hi : ip = iq := W64_inj_of_lt (by omega) (by omega) hrev.2
  subst hi
  rw [hcp] at hcq
  exact congrArg kvEncode (Option.some.inj hcq)

/-- The bucket's lookup of a change's revision is its key-value, encoded. -/
theorem bucketMap_lookup_of_BucketHas (log : Log) (hwf : LogWf log) (hlen : log.length < 2 ^ 63)
    (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) (rev : Rev) (kv : EtcdKv)
    (h : BucketHas log rev kv) (hmod : kv.modRev = rev.main) :
    (bucketMap log).lookup (revBytes rev false) = some (kvEncode kv) := by
  apply bucketMap_lookup_of_mem _ _ _ (bucketOf_mem_of_BucketHas log hwf rev kv h hmod)
  intro p hp hk
  exact bucketOf_fun log hlen hcs p hp _ (bucketOf_mem_of_BucketHas log hwf rev kv h hmod) hk

/-! ## The limited answers -/

/-- No answer taken, none counted. -/
theorem rangeTotal_of_taken_nil (log : Log) (endNil : Bool) (k e : GoString) (atRev limit : w64)
    (withTotal : Bool) (h : rangeTaken log endNil k e atRev limit = []) :
    rangeTotal log endNil k e atRev limit withTotal = 0 := by
  unfold rangeTaken at h
  unfold rangeTotal
  cases endNil with
  | true => simp only [↓reduceIte] at h ⊢; rw [h]; rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    unfold limitOf at h ⊢
    split at h
    · rename_i hpos
      simp only [takeLimit, List.take_eq_nil_iff] at h
      rcases h with h | h
      · exfalso; omega
      · simp only [hpos, ↓reduceIte, h, List.length_nil]; cases withTotal <;> rfl
    · rename_i hneg
      simp only [takeLimit] at h
      simp only [hneg, ↓reduceIte, h, List.length_nil]; cases withTotal <;> rfl

/-- A taken answer is an answer. -/
theorem mem_rangeAnswers_of_taken (log : Log) (endNil : Bool) (k e : GoString) (atRev limit : w64)
    (a : GoString × Rev × Rev × w64) (h : a ∈ rangeTaken log endNil k e atRev limit) :
    a ∈ rangeAnswers log endNil k e atRev := by
  unfold rangeTaken at h
  cases endNil with
  | true => simpa using h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    unfold takeLimit at h
    split at h
    · exact List.mem_of_mem_take h
    · exact h

/-! ## Filling a slice of pointers in order -/

/-- Setting the slot after the `i` filled ones (the rest still `null`). -/
theorem set_filled {ps : List Loc} {i n : Nat} (hps : ps.length = i) (hin : i < n) (p : Loc) :
    (ps ++ List.replicate (n - i) (zero_val Loc)).set i p =
      (ps ++ [p]) ++ List.replicate (n - (i + 1)) (zero_val Loc) := by
  rw [List.set_append_right _ _ (by omega), hps, Nat.sub_self,
    show n - i = (n - (i + 1)) + 1 by omega, List.replicate_succ, List.set_cons_zero,
    List.append_assoc, List.singleton_append]

/-- A found key-value's key. -/
theorem findKey_key {k : GoString} {s : List EtcdKv} {kv : EtcdKv} (h : findKey k s = some kv) :
    kv.key = k := by
  unfold findKey at h
  simpa using List.find?_some h

/-- `sliceCapWithLimit(limit, s)`: `len(s)` unless `limit` is positive and smaller. -/
def capWithLimit (limit : w64) (n : Nat) : Nat :=
  if sint.Z limit ≤ 0 ∨ (n : Int) < sint.Z limit then n else (sint.Z limit).toNat

/-- At most one answer without an end key. -/
theorem rangeAnswers_nil_length_le (log : Log) (k e : GoString) (atRev : w64) :
    (rangeAnswers log true k e atRev).length ≤ 1 := by
  rw [rangeAnswers_nil]
  cases kiGet (kiOfKey (evsOf log) k) atRev <;> simp

/-- The taken answers are within the limit: `sliceCapWithLimit` keeps them all. -/
theorem capWithLimit_rangeTaken (log : Log) (endNil : Bool) (k e : GoString) (atRev limit : w64) :
    capWithLimit limit (rangeTaken log endNil k e atRev limit).length =
      (rangeTaken log endNil k e atRev limit).length := by
  unfold capWithLimit
  split
  · rfl
  · rename_i h
    have hpos : 0 < sint.Z limit := by omega
    have hle : sint.Z limit ≤ (rangeTaken log endNil k e atRev limit).length := by omega
    unfold rangeTaken at hle ⊢
    cases endNil with
    | true =>
      simp only [↓reduceIte] at hle ⊢
      have := rangeAnswers_nil_length_le log k e atRev
      omega
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hle ⊢
      rw [takeLimit_length] at hle ⊢
      unfold limitOf totalOf at hle ⊢
      simp only [hpos, ↓reduceIte] at hle ⊢
      omega

/-! ## The answers of a range read -/

theorem LogWf.of_wf' {log : Log} (h : LogWf' log) (hne : log ≠ []) : LogWf log :=
  ⟨h.1 hne, h.2⟩

/-- Every answer `(key, (mod, created, ver))` of a range read at revision `r` has its
key-value: in the state at `r`, with those revisions and version, and encoded in the bucket
at `mod`'s bytes. -/
theorem rangeAnswers_kv (log : Log) (hwf : LogWf log) (hlen : log.length < 2 ^ 63)
    (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) (endNil : Bool) (k e : GoString) (r : Nat)
    (hr : r < 2 ^ 63) :
    ∀ a ∈ rangeAnswers log endNil k e (W64 r), ∃ kv : EtcdKv,
      findKey a.1 (stateAt log r) = some kv ∧ kv.modRev = a.2.1.main ∧
      kv.createRev = a.2.2.1.main ∧ kv.version = a.2.2.2 ∧
      (bucketMap log).lookup (revBytes a.2.1 false) = some (kvEncode kv) := by
  rintro ⟨key, m, c, v⟩ ha
  simp only
  -- the answer is `kiGet` of the key's index
  have hget : (idxGet (indexOf (evsOf log)) key).bind (fun ki => kiGet ki (W64 r)) =
      some (m, c, v) := by
    cases endNil with
    | true =>
      rw [rangeAnswers_nil, Option.mem_toList] at ha
      cases hg : kiGet (kiOfKey (evsOf log) k) (W64 r) with
      | none => rw [hg] at ha; simp at ha
      | some ans =>
        rw [hg] at ha
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        rw [idxGet_indexOf_bind]
        exact hg
    | false =>
      unfold rangeAnswers at ha
      simp only [Bool.false_eq_true, ↓reduceIte] at ha
      unfold rangeAt at ha
      rw [List.mem_filterMap] at ha
      obtain ⟨z, hz, hza⟩ := ha
      rw [List.mem_filter] at hz
      cases hg : kiGet z.2 (W64 r) with
      | none => rw [hg] at hza; simp at hza
      | some ans =>
        rw [hg] at hza
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hza
        obtain ⟨rfl, rfl⟩ := hza
        rw [idxGet_of_mem _ (indexOf_sorted _) z hz.1]
        exact hg
  have hm := kiGet_indexOf log hlen hcs hwf key r hr
  rw [hget] at hm
  cases hf : findKey key (stateAt log r) with
  | none => rw [hf] at hm; simp [KvMatch] at hm
  | some kv =>
    rw [hf] at hm
    obtain ⟨hmod, hcr, hver, hb⟩ := hm
    exact ⟨kv, rfl, hmod, hcr, hver, bucketMap_lookup_of_BucketHas log hwf hlen hcs m kv hb hmod⟩

/-! ### The pending revision grows: well-formedness -/

/-- The state the pending revision's changes act on: after the committed log. -/
theorem stateAt_pend (ilog : Log) (pend : List Change) :
    stateAt (ilog ++ [pend]) ilog.length = applyChanges (W64 ilog.length) (stateAfter ilog) pend :=
  stateAt_append_ge ilog pend (Nat.le_refl _)

/-- A change appended to the pending revision keeps the log well formed, if it is a put, or a
delete of a key present after the pending changes. -/
theorem LogWf'.append_change {ilog : Log} {pend : List Change} (h : LogWf' (ilog ++ [pend]))
    (hne : ilog ≠ []) (c : Change)
    (hc : ∀ k, c = .del k →
      (findKey k (applyChanges (W64 ilog.length) (stateAfter ilog) pend)).isSome) :
    LogWf' (ilog ++ [pend ++ [c]]) := by
  have hpos : 0 < ilog.length := List.length_pos_iff.2 hne
  refine ⟨fun _ => ?_, fun r cs i k hr hi => ?_⟩
  · have := h.1 (by simp)
    rw [List.getElem?_append_left hpos] at this ⊢
    exact this
  · by_cases hlt : r < ilog.length
    · rw [List.getElem?_append_left hlt] at hr
      have := h.2 r cs i k (by rw [List.getElem?_append_left hlt]; exact hr) hi
      rw [stateAt_append_lt _ _ (by omega)] at this ⊢
      exact this
    · rw [List.getElem?_append_right (by omega)] at hr
      have hr0 : r - ilog.length = 0 := by
        have := (List.getElem?_eq_some_iff.1 hr).1
        simp at this; omega
      rw [hr0] at hr
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
      subst hr
      have hreq : r = ilog.length := by omega
      subst hreq
      rw [stateAt_append_lt _ _ (by omega), stateAt_last]
      by_cases hil : i < pend.length
      · rw [List.getElem?_append_left hil] at hi
        rw [List.take_append_of_le_length (by omega)]
        have := h.2 ilog.length pend i k
          (by rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl) hi
        rw [stateAt_append_lt _ _ (by omega), stateAt_last] at this
        exact this
      · rw [List.getElem?_append_right (by omega)] at hi
        have hi0 : i - pend.length = 0 := by
          have := (List.getElem?_eq_some_iff.1 hi).1
          simp at this; omega
        rw [hi0] at hi
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        have hieq : i = pend.length := by omega
        subst hieq
        rw [List.take_left]
        exact hc k hi

/-! ## The write transaction: the pending revision -/

/-- A word from its non-negative signed value. -/
theorem W64_sint_nat (x : w64) (h : 0 ≤ sint.Z x) : W64 (sint.nat x : Int) = x := by
  have := Int.toNat_of_nonneg h
  show BitVec.ofInt 64 ((sint.Z x).toNat : Int) = x
  rw [this]
  exact BitVec.ofInt_toInt

/-- The revision a write transaction reads the index at (`deleteRange`'s `rrev`, `Range`'s
`rev`): the pending revision once it has a change, else the committed log's last. -/
def writeRev (ilog : Log) (pend : List Change) : Nat :=
  if pend = [] then ilog.length - 1 else ilog.length

theorem writeRev_lt (ilog : Log) (pend : List Change) (hne : ilog ≠ []) :
    writeRev ilog pend < (ilog ++ [pend]).length := by
  have := List.length_pos_iff.2 hne
  unfold writeRev; split <;> simp <;> omega

/-- The state at `writeRev`: after the pending changes. -/
theorem stateAt_writeRev (ilog : Log) (pend : List Change) (hne : ilog ≠ []) :
    stateAt (ilog ++ [pend]) (writeRev ilog pend) =
      applyChanges (W64 ilog.length) (stateAfter ilog) pend := by
  have := List.length_pos_iff.2 hne
  unfold writeRev
  split
  · subst pend
    rw [stateAt_append_lt _ _ (by omega), stateAt_last]; rfl
  · exact stateAt_pend ilog pend

/-- The keys `deleteRange` deletes: the index's answers in the range at `writeRev`, in key
order. -/
def delKeys (ilog : Log) (pend : List Change) (endNil : Bool) (k e : GoString) : List GoString :=
  (rangeTaken (ilog ++ [pend]) endNil k e (W64 (writeRev ilog pend)) (W64 0)).map Prod.fst

/-- Every key to delete is present after the pending changes. -/
theorem delKeys_present (ilog : Log) (pend : List Change) (endNil : Bool) (k e : GoString)
    (hwf : LogWf (ilog ++ [pend])) (hlen : (ilog ++ [pend]).length < 2 ^ 63)
    (hcs : ∀ cs ∈ ilog ++ [pend], cs.length < 2 ^ 63) (hne : ilog ≠ []) :
    ∀ kk ∈ delKeys ilog pend endNil k e,
      (findKey kk (applyChanges (W64 ilog.length) (stateAfter ilog) pend)).isSome := by
  intro kk hkk
  unfold delKeys at hkk
  rw [List.mem_map] at hkk
  obtain ⟨a, ha, rfl⟩ := hkk
  have hmem := mem_rangeAnswers_of_taken _ _ _ _ _ _ a ha
  have hlt := writeRev_lt ilog pend hne
  obtain ⟨kv, hfind, -⟩ := rangeAnswers_kv (ilog ++ [pend]) hwf hlen hcs endNil k e
    (writeRev ilog pend) (by omega) a hmem
  rw [stateAt_writeRev ilog pend hne] at hfind
  rw [hfind]; rfl

theorem rangeAt_keys_sublist (idx : IndexM) (k e : GoString) (atRev : w64) :
    ((rangeAt idx k e atRev).map Prod.fst).Sublist (idx.map Prod.fst) := by
  unfold rangeAt
  induction idx with
  | nil => simp
  | cons z zs ih =>
    rw [List.filter_cons]
    split
    · rw [List.filterMap_cons, List.map_cons]
      cases kiGet z.2 atRev with
      | none => exact ih.cons _
      | some r => simp only [Option.map_some, List.map_cons]; exact ih.cons₂ _
    · rw [List.map_cons]; exact ih.cons _

/-- The keys to delete are distinct (the index's keys are sorted). -/
theorem delKeys_nodup (ilog : Log) (pend : List Change) (endNil : Bool) (k e : GoString) :
    (delKeys ilog pend endNil k e).Nodup := by
  unfold delKeys rangeTaken
  cases endNil with
  | true =>
    simp only [↓reduceIte, rangeAnswers]
    cases kiGet (kiOfKey (evsOf (ilog ++ [pend])) k) (W64 (writeRev ilog pend)) <;> simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, rangeAnswers]
    have h1 : (takeLimit (limitOf (W64 0))
        (rangeAt (indexOf (evsOf (ilog ++ [pend]))) k e (W64 (writeRev ilog pend)))).Sublist
        (rangeAt (indexOf (evsOf (ilog ++ [pend]))) k e (W64 (writeRev ilog pend))) := by
      unfold takeLimit; split
      · exact List.take_sublist _ _
      · exact List.Sublist.refl _
    exact (nodup_of_sorted (keys_sorted _)).sublist
      ((h1.map Prod.fst).trans (rangeAt_keys_sublist _ k e _))

/-- Deleting other keys keeps a key's key-value. -/
theorem findKey_applyChanges_dels (r : w64) (k : GoString) :
    ∀ (ks : List GoString) (s : List EtcdKv), k ∉ ks →
      findKey k (applyChanges r s (ks.map .del)) = findKey k s
  | [], s, _ => rfl
  | k' :: ks, s, hk => by
    rw [List.map_cons]
    unfold applyChanges
    rw [List.foldl_cons]
    have ih := findKey_applyChanges_dels r k ks (applyChange r s (.del k'))
      (fun h => hk (List.mem_cons_of_mem _ h))
    unfold applyChanges at ih
    rw [ih]
    simp only [applyChange]
    rw [findKey_filter_ne]
    have : k' ≠ k := fun h => hk (h ▸ List.mem_cons_self)
    simp [this]

/-- A change's key-value is unchanged by later changes of the revision. -/
theorem changeKv_append_lt (r : w64) (s : List EtcdKv) (cs : List Change) (c : Change) {i : Nat}
    (hi : i < cs.length) : changeKv r s (cs ++ [c]) i = changeKv r s cs i := by
  unfold changeKv
  rw [List.getElem?_append_left hi, List.take_append_of_le_length (by omega)]

/-- The entries a write transaction has put: the pending revision's. -/
def pendPuts (ilog : Log) (pend : List Change) : List (GoString × GoString) :=
  bucketOfRev ilog.length (stateAfter ilog) pend

theorem pendPuts_nil (ilog : Log) : pendPuts ilog [] = [] := rfl

/-- The entries after one more change: one more entry, at the change's revision bytes. -/
theorem pendPuts_append (ilog : Log) (pend : List Change) (c : Change) (kv : EtcdKv)
    (hkv : changeKv (W64 ilog.length) (stateAfter ilog) (pend ++ [c]) pend.length = some kv) :
    pendPuts ilog (pend ++ [c]) =
      pendPuts ilog pend ++ [(revBytes ⟨W64 ilog.length, W64 pend.length⟩ c.isDel, kvEncode kv)] := by
  unfold pendPuts bucketOfRev
  rw [List.zipIdx_append, List.filterMap_append]
  congr 1
  · apply filterMap_congr'
    intro p hp
    rw [List.mem_zipIdx_iff_getElem?] at hp
    have hlt : p.2 < pend.length := (List.getElem?_eq_some_iff.1 hp).1
    rw [changeKv_append_lt _ _ _ _ hlt]
  · simp only [List.zipIdx_cons, List.zipIdx_nil, Nat.zero_add, List.filterMap_cons,
      List.filterMap_nil]
    rw [hkv]
    rfl

/-- The bucket of the log with the pending revision committed: the old entries, then the
pending puts. -/
theorem bucketOf_append (ilog : Log) (pend : List Change) (hne : ilog ≠ []) :
    bucketOf (ilog ++ [pend]) = bucketOf ilog ++ pendPuts ilog pend := by
  have hpos := List.length_pos_iff.2 hne
  unfold bucketOf pendPuts
  rw [List.zipIdx_append, List.map_append, List.flatten_append]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro p hp
    rw [List.mem_zipIdx_iff_getElem?] at hp
    have hlt : p.2 < ilog.length := (List.getElem?_eq_some_iff.1 hp).1
    rw [stateAt_append_lt _ _ (by omega)]
  · simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, Nat.zero_add]
    rw [stateAt_append_lt _ _ (by omega), stateAt_last]

theorem bucketMap_append (ilog : Log) (pend : List Change) (hne : ilog ≠ []) :
    bucketMap (ilog ++ [pend]) =
      (pendPuts ilog pend).foldl (fun m p => GMap.insert p.1 p.2 m) (bucketMap ilog) := by
  unfold bucketMap
  rw [bucketOf_append ilog pend hne, List.foldl_append]

theorem applyChanges_append_singleton (r : w64) (s : List EtcdKv) (cs : List Change) (c : Change) :
    applyChanges r s (cs ++ [c]) = applyChange r (applyChanges r s cs) c := by
  unfold applyChanges; rw [List.foldl_append]; rfl

/-- `findKey` of the put key after `putKv`, as a value. -/
theorem findKey_putKv_self_eq {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (r : w64)
    (k v : GoString) (l : w64) :
    findKey k (putKv r k v l s) = some (match findKey k s with
      | some old => { old with modRev := r, version := old.version + W64 1, value := v, lease := l }
      | none => { key := k, createRev := r, modRev := r, version := W64 1, value := v, lease := l }) := by
  unfold putKv
  simp only
  rw [findKey_btInsert _ s hs]
  unfold findKey
  cases h : s.find? (fun v => decide (v.key = k)) with
  | none => simp
  | some old =>
    have hk : old.key = k := by simpa using List.find?_some h
    simp [hk]

/-- The key-value `put` writes for `k`, given the index's answer of `k` at the pending revision
`r`: created and versioned after the answer, or new. -/
def putKvOf (k v : GoString) (l : w64) (r : w64) : Option (Rev × Rev × w64) → EtcdKv
  | some (_, c, ver) =>
    { key := k, createRev := c.main, modRev := r, version := ver + W64 1, value := v, lease := l }
  | none => { key := k, createRev := r, modRev := r, version := W64 1, value := v, lease := l }

/-- What `put` writes: the pending revision's new put of `k`, from the index's answer of the
key at the pending revision (the writer's log `ilog ++ [pend]`). -/
theorem changeKv_put (ilog : Log) (pend : List Change) (k v : GoString) (l : w64)
    (hwf : LogWf (ilog ++ [pend])) (hlen : (ilog ++ [pend]).length < 2 ^ 63)
    (hcs : ∀ cs ∈ ilog ++ [pend], cs.length < 2 ^ 63) :
    changeKv (W64 ilog.length) (stateAfter ilog) (pend ++ [.put k v l]) pend.length =
      some (putKvOf k v l (W64 ilog.length)
        (kiGet (kiOfKey (evsOf (ilog ++ [pend])) k) (W64 ilog.length))) := by
  have hm := kiGet_indexOf (ilog ++ [pend]) hlen hcs hwf k ilog.length (by simp at hlen; omega)
  rw [idxGet_indexOf_bind, stateAt_pend] at hm
  unfold changeKv
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  simp only [List.getElem?_cons_zero]
  rw [List.take_of_length_le (by simp), applyChanges_append_singleton]
  simp only [applyChange]
  have hs := applyChanges_sorted (W64 ilog.length) pend (stateAfter_sorted ilog)
  rw [findKey_putKv_self_eq hs]
  cases hg : kiGet (kiOfKey (evsOf (ilog ++ [pend])) k) (W64 ilog.length) with
  | none =>
    rw [hg] at hm
    rw [KvMatch_none_left hm]
    rfl
  | some a =>
    obtain ⟨m, c, ver⟩ := a
    rw [hg] at hm
    cases hf : findKey k (applyChanges (W64 ilog.length) (stateAfter ilog) pend) with
    | none => rw [hf] at hm; simp [KvMatch] at hm
    | some old =>
      rw [hf] at hm
      obtain ⟨-, hocr, hover, -⟩ := hm
      have hk := findKey_key hf
      simp only [putKvOf]
      congr 1
      cases old
      simp only at hk hocr hover
      subst hk hocr hover
      rfl

end mvcc
end EtcdGrove
end Perennial
