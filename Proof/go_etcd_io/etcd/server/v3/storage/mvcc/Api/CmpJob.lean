/-
**The compaction job's tracked compaction** (the snapshot image's tracking, the job, 2026-11-06;
`notes/mvcc-api-invariants.md`, "the job's tracking"). Lean-first (no Rocq counterpart).

The job (`store.scheduleCompaction`) deletes, in batches under the batch lock, the `Key` entries up
to its revision `c₁` that compaction at `c₁` does not keep. The batch lock's resource pins the cut of
the physical bucket (`cmpTrack`, `snap.cmpOk`) with the last job's revision and cursor `jc`; the
job's own half of the cursor (`jobCur`, in `compactTok`) lets it find its cursor between batches.
* Pure (`snap`): the cursor's order on the bucket's keys (`rb_lt`, `rb_le`, `zeros_le`,
  `revSucc_lt`); a batch's entries, read from the cursor in key order and covering the physical
  bucket (`job_gap`: no physical entry between the cursor and the entry at hand); one entry's step
  (`cmpOk_step`: deleted, `cutAt_del`; or kept); the job's start (`cmpOk_start`, its cursor at
  `⟨0, 0⟩`).
* Iris: the session's tracked compaction (`sessTrk`: the cursor's ghost whole, held by the job for
  the session), opened from the lock's (`sess_open`), stepped (`sess_mono`), finished (`sess_fin`:
  `cmpOk_fin`) and closed (`sess_close`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.CmpSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RevOrder
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace snap

open Iris Iris.BI Iris.ProofMode

section pure
variable [GooseExts]

/-- A revision of the log's entries: non-negative, with room for its successor's sub-revision. -/
def RevOk (r : Rev) : Prop := 0 ≤ sint.Z r.main ∧ 0 ≤ sint.Z r.sub ∧ sint.Z r.sub < 2 ^ 63 - 1

/-- The job's cursor just past `r` (the next batch's first key: `revOf ⟨Main, Sub + 1⟩`). -/
def revSucc (r : Rev) : Rev := ⟨r.main, r.sub + W64 1⟩

theorem w64_eq_of_sint {x y : w64} (h : sint.Z x = sint.Z y) : x = y := by
  apply BitVec.eq_of_toInt_eq; exact h

theorem uint_of_sint {x : w64} (h : 0 ≤ sint.Z x) : uint.Z x = sint.Z x := by word

/-- Two revisions neither below the other are equal. -/
theorem rev_trich {a b : Rev} (h1 : ¬ Rev.lt a b) (h2 : ¬ Rev.lt b a) : a = b := by
  unfold Rev.lt at h1 h2
  have hm : sint.Z a.main = sint.Z b.main := by
    rcases Int.lt_trichotomy (sint.Z a.main) (sint.Z b.main) with h | h | h
    · exact absurd (Or.inl h) h1
    · exact h
    · exact absurd (Or.inl h) h2
  have hm' := w64_eq_of_sint hm
  have hs : sint.Z a.sub = sint.Z b.sub := by
    rcases Int.lt_trichotomy (sint.Z a.sub) (sint.Z b.sub) with h | h | h
    · exact absurd (Or.inr ⟨hm', h⟩) h1
    · exact h
    · exact absurd (Or.inr ⟨hm'.symm, h⟩) h2
  have hs' := w64_eq_of_sint hs
  cases a; cases b; simp only at hm' hs'; subst hm' hs'; rfl

theorem revSucc_lt {a r : Rev} (hr : RevOk r) :
    Rev.lt a (revSucc r) ↔ Rev.lt a r ∨ a = r := by
  obtain ⟨-, h1, h2⟩ := hr
  have hs : sint.Z (r.sub + W64 1) = sint.Z r.sub + 1 := by word
  unfold Rev.lt revSucc
  simp only [hs]
  constructor
  · rintro (h | ⟨hm, h⟩)
    · exact Or.inl (Or.inl h)
    · by_cases he : sint.Z a.sub < sint.Z r.sub
      · exact Or.inl (Or.inr ⟨hm, he⟩)
      · right
        have hss := w64_eq_of_sint (show sint.Z a.sub = sint.Z r.sub by omega)
        cases a; cases r; simp only at hm hss; subst hm hss; rfl
  · rintro ((h | ⟨hm, h⟩) | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨hm, by omega⟩
    · exact Or.inr ⟨rfl, by omega⟩

/-- **The keys are ordered by their revisions** (non-negative ones). -/
theorem rb_lt {a b : Rev} (ha : 0 ≤ sint.Z a.main ∧ 0 ≤ sint.Z a.sub)
    (hb : 0 ≤ sint.Z b.main ∧ 0 ≤ sint.Z b.sub) (h : Rev.lt a b) (ta tb : Bool) :
    go.GoStringLt (revBytes a ta) (revBytes b tb) := by
  apply RevOrder.revBytes_lt
  rw [uint_of_sint ha.1, uint_of_sint hb.1, uint_of_sint ha.2, uint_of_sint hb.2]
  exact h

/-- A key at or past the cursor's revision is at or past the cursor's key. -/
theorem rb_le {p r : Rev} (hp : 0 ≤ sint.Z p.main ∧ 0 ≤ sint.Z p.sub)
    (hr : 0 ≤ sint.Z r.main ∧ 0 ≤ sint.Z r.sub) (h : ¬ Rev.lt r p) (t : Bool) :
    go.GoStringLe (revBytes p false) (revBytes r t) := by
  by_cases hlt : Rev.lt p r
  · exact Or.inr (rb_lt hp hr hlt false t)
  · have := rev_trich h hlt
    subst this
    cases t
    · exact Or.inl rfl
    · right
      unfold revBytes
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact RevOrder.lex_prefix _ List.Lex.nil

/-- The job's first key (`make([]byte, 17)`) is below every key. -/
theorem zeros_le (r : Rev) (t : Bool) : go.GoStringLe (List.replicate 17 (W8 0)) (revBytes r t) := by
  right
  have hz : List.replicate 17 (W8 0) = u64Be (W64 0) ++ ([W8 0] ++ u64Be (W64 0)) := by decide
  rw [hz]
  unfold revBytes
  simp only [List.append_assoc]
  by_cases h0 : uint.Z r.main = 0
  · have : r.main = W64 0 := by word
    rw [this]
    apply RevOrder.u64Be_eq_lt
    simp only [List.singleton_append, List.cons_append]
    exact List.Lex.rel (by decide)
  · apply RevOrder.u64Be_lt
    word

/-- In a list strictly ordered by keys, a member below the `i`th entry's key is an earlier entry. -/
theorem range_before {R : List (GoString × GoString)} (hs : (R.map Prod.fst).Pairwise go.GoStringLt)
    {i : Nat} (hi : i < R.length) {k' v' : GoString} (hm : (k', v') ∈ R)
    (hlt : go.GoStringLt k' (R[i]).1) : ∃ (j : Nat) (hj : j < i), (R[j]'(by omega)).1 = k' := by
  obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hm
  have hsrt := List.pairwise_iff_getElem.1 hs
  rcases Nat.lt_trichotomy j i with h | h | h
  · exact ⟨j, h, by rw [hjeq]⟩
  · subst h; rw [hjeq] at hlt; exact absurd hlt (go.goStringLt_irrefl _)
  · exfalso
    have := hsrt i j (by simpa using hi) (by simpa using hj) h
    simp only [List.getElem_map, hjeq] at this
    exact go.goStringLt_asymm this hlt

/-- **No physical entry between the cursor `pc` and the entry `r`** at hand (the deleted entries
`X`). -/
def gapOk (m : Bucket) (X : backend.VData) (pc r : Rev) : Prop :=
  ∀ (r' : Rev) (t' : Bool), 0 ≤ sint.Z r'.main → 0 ≤ sint.Z r'.sub →
    physLookup m X (revBytes r' t') ≠ none → ¬ Rev.lt r' pc → ¬ Rev.lt r' r

/-- **The batch's first key `bs` is the cursor `pc`'s** (the job's first: `make([]byte, 17)`, at
`⟨0, 0⟩`). -/
def bsCur (bs : GoString) (pc : Rev) : Prop :=
  (bs = List.replicate 17 (W8 0) ∧ pc = ⟨W64 0, W64 0⟩) ∨
  (bs = revBytes pc false ∧ 0 ≤ sint.Z pc.main ∧ 0 ≤ sint.Z pc.sub)

/-- **A batch's gap** (`kvstore_compaction.go`'s loop): the batch's entries are the first `n` of the
range from `bs` of the bucket `m'`, which holds every physical entry at `X0` (the compacting
range's exactness); so between the cursor (the batch's first key's, or just past the entry before)
and the `i`th entry, no physical entry at `X ⊇ X0`. -/
theorem job_gap {m m' : Bucket} {X0 X : backend.VData} {bs khi : GoString} {n : Nat}
    (hex : ∀ k, physLookup m X0 k ≠ none → (m'.lookup k).isSome)
    (hXX : ∀ k, (X0.lookup (keyName, k)).isSome → (X.lookup (keyName, k)).isSome)
    {Lb : List (GoString × GoString)} (hLb : (bucketRange m' bs khi).take n = Lb)
    {i : Nat} (hi : i < Lb.length)
    {r : Rev} {t : Bool} (hk : (Lb[i]).1 = revBytes r t)
    (hr : 0 ≤ sint.Z r.main ∧ 0 ≤ sint.Z r.sub) {pc : Rev}
    (hcur : (i = 0 ∧ bsCur bs pc) ∨
      (∃ (r0 : Rev) (t0 : Bool), 0 < i ∧
        (Lb[i - 1]?).map Prod.fst = some (revBytes r0 t0) ∧ RevOk r0 ∧
        pc = revSucc r0)) :
    gapOk m X pc r := by
  subst hLb
  replace hcur : (i = 0 ∧ bsCur bs pc) ∨
      (∃ (r0 : Rev) (t0 : Bool), 0 < i ∧
        (((bucketRange m' bs khi).take n)[i - 1]'(by omega)).1 = revBytes r0 t0 ∧ RevOk r0 ∧
        pc = revSucc r0) := by
    rcases hcur with h | ⟨r0, t0, h0, hk0, hr0, hpc⟩
    · exact Or.inl h
    · refine Or.inr ⟨r0, t0, h0, ?_, hr0, hpc⟩
      rw [List.getElem?_eq_getElem (by omega)] at hk0
      simpa using hk0
  intro r' t' h0 h1 hph hge hlt'
  have hRe := (bucketRange_eq_iff m' bs khi (bucketRange m' bs khi)).1 rfl
  have hiR : i < (bucketRange m' bs khi).length := by
    have := hi; simp only [List.length_take] at this; omega
  have hLi : ((bucketRange m' bs khi).take n)[i] = (bucketRange m' bs khi)[i] :=
    List.getElem_take ..
  rw [hLi] at hk
  have hmemi := (hRe.2 ((bucketRange m' bs khi)[i]).1 ((bucketRange m' bs khi)[i]).2).1
    (List.getElem_mem hiR)
  rw [hk] at hmemi
  -- the physical entry `k'` is the range bucket's
  have hph0 : physLookup m X0 (revBytes r' t') ≠ none := by
    intro hn; apply hph
    unfold physLookup at hn ⊢
    cases hx : (X0.lookup (keyName, revBytes r' t')).isSome with
    | true => rw [hXX _ hx]; rfl
    | false =>
      rw [hx] at hn
      simp only [Bool.false_eq_true, ↓reduceIte] at hn
      split <;> first | rfl | exact hn
  obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.1 (hex _ hph0)
  have hkk : go.GoStringLt (revBytes r' t') (revBytes r t) := rb_lt ⟨h0, h1⟩ hr hlt' t' t
  -- at or past the batch's first key
  have hbs : go.GoStringLe bs (revBytes r' t') := by
    rcases hcur with ⟨-, ⟨rfl, -⟩ | ⟨rfl, hp0, hp1⟩⟩ | ⟨r0, t0, hi0, hk0, hr0, rfl⟩
    · exact zeros_le r' t'
    · exact rb_le ⟨hp0, hp1⟩ ⟨h0, h1⟩ hge t'
    · have hlt0 : Rev.lt r0 r' := by
        rw [revSucc_lt hr0] at hge
        apply Classical.byContradiction; intro hn
        rcases (Classical.em (Rev.lt r' r0)) with h | h
        · exact hge (Or.inl h)
        · exact hge (Or.inr (rev_trich h hn))
      have hL0 : ((bucketRange m' bs khi).take n)[i - 1]'(by omega) =
          (bucketRange m' bs khi)[i - 1]'(by omega) := List.getElem_take ..
      rw [hL0] at hk0
      have hm0 := (hRe.2 ((bucketRange m' bs khi)[i - 1]'(by omega)).1
        ((bucketRange m' bs khi)[i - 1]'(by omega)).2).1
        (List.getElem_mem (show i - 1 < (bucketRange m' bs khi).length by omega))
      rw [hk0] at hm0
      exact goStringLe_trans hm0.2.1 (Or.inr (rb_lt ⟨hr0.1, hr0.2.1⟩ ⟨h0, h1⟩ hlt0 t0 t'))
  have hmem : (revBytes r' t', v') ∈ bucketRange m' bs khi :=
    (hRe.2 _ _).2 ⟨hv', hbs, go.goStringLt_trans hkk hmemi.2.2⟩
  obtain ⟨j, hj, hjk⟩ := range_before hRe.1 hiR hmem (by rw [hk]; exact hkk)
  rcases hcur with ⟨rfl, -⟩ | ⟨r0, t0, hi0, hk0, hr0, rfl⟩
  · omega
  · have hL0 : ((bucketRange m' bs khi).take n)[i - 1]'(by omega) =
        (bucketRange m' bs khi)[i - 1]'(by omega) := List.getElem_take ..
    rw [hL0] at hk0
    have hlt0 : Rev.lt r0 r' := by
      rw [revSucc_lt hr0] at hge
      apply Classical.byContradiction; intro hn
      rcases (Classical.em (Rev.lt r' r0)) with h | h
      · exact hge (Or.inl h)
      · exact hge (Or.inr (rev_trich h hn))
    have hk0' : go.GoStringLt (revBytes r0 t0) (revBytes r' t') :=
      rb_lt ⟨hr0.1, hr0.2.1⟩ ⟨h0, h1⟩ hlt0 t0 t'
    rcases Nat.lt_or_ge j (i - 1) with hji | hji
    · have hsrt := List.pairwise_iff_getElem.1 hRe.1
      have := hsrt j (i - 1) (by simp; omega) (by simp; omega) hji
      simp only [List.getElem_map, hjk, hk0] at this
      exact go.goStringLt_asymm this hk0'
    · have hj' : j = i - 1 := by omega
      subst hj'
      rw [hk0] at hjk
      rw [hjk] at hk0'
      exact go.goStringLt_irrefl _ hk0'

/-- Deletability does not depend on the tombstone mark. -/
theorem KeyDel_tomb {L : Log} {c : Int} {r : Rev} {t : Bool} (t' : Bool)
    (h : KeyDel L c (revBytes r t)) : KeyDel L c (revBytes r t') := by
  obtain ⟨hc, r2, t2, he, h0, h1, hk⟩ := h
  obtain ⟨-, rfl⟩ := revBytes_inj _ _ _ _ he
  exact ⟨hc, r, t', rfl, h0, h1, hk⟩

/-- A key of the log's bucket is an entry's. -/
theorem bucketMap_ent {L : Log} (hb : LogB L) {k v : GoString} (h : (bucketMap L).lookup k = some v) :
    ∃ x ∈ logEnts L 0 L.length, x.pair = (k, v) := by
  rw [← bucketOfEnts_logEnts] at h
  exact List.mem_map.1 ((bucketOfEnts_lookup_iff L hb (List.Sublist.refl _) k v).1 h)

/-- An entry's revision is a log entry's: non-negative, its sub below `2 ^ 63 - 1`. -/
theorem ent_revOk {L : Log} (hb : LogB L) {x : KvEnt} (hx : x ∈ logEnts L 0 L.length) :
    RevOk x.rev := by
  obtain ⟨j, i, c, kv, -, -, hj, hgj, -, hc, -, rfl⟩ := logEnts_entry L 0 L.length x hx
  have hcl := hb.2 _ (List.mem_of_getElem? hgj)
  have hil : i < (L.getD j []).length := (List.getElem?_eq_some_iff.1 hc).1
  have hl := hb.1
  refine ⟨?_, ?_, ?_⟩ <;> simp only <;> word

/-- A key of the log's bucket is of a log entry's revision. -/
theorem bucketMap_revOk {L : Log} (hb : LogB L) {r : Rev} {t : Bool} {v : GoString}
    (h : (bucketMap L).lookup (revBytes r t) = some v) : RevOk r := by
  obtain ⟨x, hx, hp⟩ := bucketMap_ent hb h
  obtain ⟨-, hr⟩ := revBytes_inj _ _ _ _ (congrArg Prod.fst hp)
  rw [← hr]; exact ent_revOk hb hx

/-- **One entry of the job's batch** (`r`, of the bucket of `L`): deleted (compaction at `c₁` may,
the backend records it, `X'`) or kept (it may not), the tracked compaction moves its cursor past
it. The gap (`gapOk`) gives the loop invariant below the entry (`cutAt_del`'s `hpast`). -/
theorem cmpOk_step {L : Log} (hb : LogB L) (hwf : LogWf' L) {m : Bucket} {X X' : backend.VData}
    {rc : CmpRecs} {c₁ : Int} {pc r : Rev} {t : Bool} {v : GoString}
    (h : cmpOk L m X rc (c₁, pc)) (hgap : gapOk m X pc r)
    (hmB : (bucketMap L).lookup (revBytes r t) = some v)
    (hcase : (KeyDel L c₁ (revBytes r t) ∧ ∀ k, (X'.lookup (keyName, k)).isSome =
        ((X.lookup (keyName, k)).isSome || decide (k = revBytes r t))) ∨
      (¬ KeyDel L c₁ (revBytes r t) ∧ X' = X)) :
    cmpOk L m X' rc (c₁, revSucc r) := by
  obtain ⟨x, hx, hxp⟩ := bucketMap_ent hb hmB
  have hxk : revBytes x.rev x.tomb = revBytes r t := congrArg Prod.fst hxp
  obtain ⟨hxt, hxr⟩ := revBytes_inj _ _ _ _ hxk
  have hrok : RevOk r := hxr ▸ ent_revOk hb hx
  have hL : 0 < L.length := by
    rcases Nat.eq_zero_or_pos L.length with h0 | h0
    · exfalso; rw [h0] at hx; simp [logEnts] at hx
    · exact h0
  obtain ⟨hc0, hc1⟩ := cmpOk_crev h hL
  obtain ⟨ents, hcut, hB, hrec, hpos, hX, hjp, hj0, hj1, hjf⟩ := h
  simp only at hj0 hj1 hjf hjp
  have hbd := logEnts_bounds L hb.1 hb.2 0 L.length (Nat.le_refl _)
  have hbelow : ∀ e' ∈ logEnts L 0 L.length, Rev.lt e'.rev x.rev →
      KeyDel L c₁ (revBytes e'.rev e'.tomb) → e' ∉ ents := by
    intro e' he' hlt hd hm
    by_cases hp : Rev.lt e'.rev pc
    · exact hjp e' he' hp hd hm
    · apply hgap e'.rev e'.tomb (hbd e' he').1 (hbd e' he').2 ?_ hp (hxr ▸ hlt)
      rw [hB]
      rw [(bucketOfEnts_lookup_iff L hb hcut.1 _ _).2 (List.mem_map.2 ⟨e', hm, rfl⟩)]
      simp
  rcases hcase with ⟨hdel, hX'⟩ | ⟨hkeep, rfl⟩
  · rw [← hxk] at hdel hX'
    obtain ⟨hcut', hB', hpast'⟩ := cutAt_del hb hwf hj0 hj1 hc1 hcut hB hx hdel hbelow hX'
    refine ⟨_, hcut', hB', hrec, hpos, fun k hk => ?_, fun e' he' hlt hd => ?_, hj0, hj1, hjf⟩
    · rw [hX'] at hk
      rcases Bool.or_eq_true _ _ ▸ hk with hk | hk
      · exact hX k hk
      · rw [decide_eq_true_eq] at hk; subst hk
        exact KeyDel_mono hb hj0 hj1 hc1 hdel
    · rw [revSucc_lt hrok, ← hxr] at hlt
      exact hpast' e' he' hlt hd
  · refine ⟨ents, hcut, hB, hrec, hpos, hX, fun e' he' hlt hd hm => ?_, hj0, hj1, hjf⟩
    rcases (revSucc_lt hrok).1 hlt with hl | he
    · exact hbelow e' he' (hxr ▸ hl) hd hm
    · rw [he] at hd
      exact hkeep (KeyDel_tomb t hd)

/-- **The job's start** at `c₁` (its cursor at `⟨0, 0⟩`): after the last job at `c₀ ≤ c₁`, the records'
compaction revision at least `c₁`. -/
theorem cmpOk_start {L : Log} (hb : LogB L) {m : Bucket} {X : backend.VData} {rc : CmpRecs}
    {c₀ c₁ : Int} {p₀ : Rev} (h : cmpOk L m X rc (c₀, p₀)) (h01 : c₀ ≤ c₁) (hc : c₁ ≤ rc.crev) :
    cmpOk L m X rc (c₁, ⟨W64 0, W64 0⟩) := by
  obtain ⟨ents, hcut, hB, hrec, hpos, hX, -, hj0, -, hjf⟩ := h
  simp only at hj0 hjf
  have hbd := logEnts_bounds L hb.1 hb.2 0 L.length (Nat.le_refl _)
  refine ⟨ents, hcut, hB, hrec, hpos, hX, fun e' he' hlt => ?_, by simp only; omega, hc,
    by simp only; omega⟩
  exfalso
  have := hbd e' he'
  unfold Rev.lt at hlt
  have hz : sint.Z (W64 0 : w64) = 0 := by decide
  rw [hz] at hlt
  omega

/-- The job's revision is a revision of the log. -/
theorem cmpOk_jc_lt {L : Log} {m : Bucket} {X : backend.VData} {rc : CmpRecs} {jc : Int × Rev}
    (h : cmpOk L m X rc jc) (hL : 0 < L.length) : -1 ≤ jc.1 ∧ jc.1 < L.length := by
  have := cmpOk_crev h hL
  obtain ⟨-, -, -, -, -, -, -, hj0, hj1, -⟩ := h
  exact ⟨hj0, by omega⟩

/-- Deletability at `c` is the same on two logs one a prefix of the other, both with revision `c`. -/
theorem KeyDel_conv {log ilog : Log} (hpre : log <+: ilog ∨ ilog <+: log) (hb : LogB log)
    (hbi : LogB ilog) {c : Int} (h0 : -1 ≤ c) (h1 : c < log.length) (h2 : c < ilog.length)
    (k : GoString) : KeyDel log c k ↔ KeyDel ilog c k := by
  rcases hpre with hp | hp
  · exact (KeyDel_prefix log ilog hp hbi c h0 h1 k).symm
  · exact KeyDel_prefix ilog log hp hb c h0 h2 k

/-- A revision the compaction at `c` keeps is not deletable. -/
theorem not_KeyDel_of_keep {L : Log} {c : Int} {r : Rev} (t : Bool) (h : keepAt L c r) :
    ¬ KeyDel L c (revBytes r t) := by
  rintro ⟨-, r2, t2, he, -, -, hk⟩
  obtain ⟨-, rfl⟩ := revBytes_inj _ _ _ _ he
  exact hk h

end pure

end snap

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section sess
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The job's session's tracked compaction** (a compacting real backend's; nothing otherwise):
`cmpRest`'s, with the cursor's ghost whole (the lock's half and the job's, `jobCur`), at some value,
the cut at the job's revision and cursor `jc`. -/
def sessTrk (γ : StoreNames) (L : Log) (m : Bucket) (rc : CmpRecs) (X : backend.VData)
    (jc : Int × Rev) : IProp GF :=
  match γ.kb with
  | some d => if d.cm = true then
      iprop(ghostVar γ.rcv (1 : Qp).half rc.crev ∗ monoNatAuthOwn γ.rcl 1 (crevN rc.crev) ∗
        (∃ jg : Int × Rev, ghostVar γ.jc 1 jg) ∗ ⌜snap.cmpOk L m X rc jc⌝)
    else iprop(True)
  | none => iprop(True)

/-- **A batch's session opens the job's tracking**: the lock's tracked compaction and the job's
cursor (`jcv`: the last job's, before its first batch, then its own), at the job's revision `c₁`
(the records' compaction revision at least `c₁`, `cmpLb`) and cursor `pc` (`⟨0, 0⟩` at the first
batch). -/
theorem sess_open (γ : StoreNames) (L : Log) (hb : LogB L) (m : Bucket) (rc : CmpRecs)
    (X : backend.VData) (jcv : Int × Rev) (c₁ : Int) (pc : Rev)
    (h : jcv.1 ≤ c₁ ∧ (pc = ⟨W64 0, W64 0⟩ ∨ jcv = (c₁, pc))) :
    cmpRest (GF := GF) γ L m rc X ∗ jobCur γ jcv ∗ cmpLb γ c₁ ⊢ sessTrk γ L m rc X (c₁, pc) := by
  unfold cmpRest jobCur cmpLb sessTrk
  cases hk : γ.kb with
  | none => simp only; iintro -; itrivial
  | some d =>
  by_cases hc : d.cm = true
  rotate_left
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; iintro -; itrivial
  simp only [hc, ↓reduceIte]
  iintro ⟨⟨Hr, Hl, %jc, Hj, %Hok⟩, Hj', #Hlb, %h1⟩
  ihave %Heq := ghostVar_agree γ.jc _ _ _ _ $$ Hj Hj'
  subst Heq
  ihave %Hle := monoNatLbOwn_valid γ.rcl _ _ _ $$ Hl Hlb
  ihave ⟨Hjj, -⟩ := ghostVar_join_halves γ.jc jc jc $$ [Hj Hj']
  · iframe Hj Hj'
  iframe Hr Hl
  isplitl [Hjj]
  · iexists jc; iexact Hjj
  ipureintro
  rcases h with ⟨h01, rfl | heq⟩
  · obtain ⟨c₀, p₀⟩ := jc
    have hc : c₁ ≤ rc.crev := by
      have := Hle.2; unfold crevN at this; omega
    exact snap.cmpOk_start hb Hok h01 hc
  · rw [heq] at Hok; exact Hok

/-- **The session's steps**: a pure step of the cut. -/
theorem sess_mono (γ : StoreNames) (L : Log) (m : Bucket) (rc : CmpRecs) (X X' : backend.VData)
    (jc jc' : Int × Rev) (h : snap.cmpOk L m X rc jc → snap.cmpOk L m X' rc jc') :
    sessTrk (GF := GF) γ L m rc X jc ⊢ sessTrk γ L m rc X' jc' := by
  unfold sessTrk
  cases hk : γ.kb with
  | none => simp only; iintro -; itrivial
  | some d =>
  by_cases hc : d.cm = true
  rotate_left
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; iintro -; itrivial
  simp only [hc, ↓reduceIte]
  iintro ⟨Hr, Hl, Hj, %Hok⟩
  iframe Hr Hl Hj
  ipureintro; exact h Hok

/-- **The job's last batch**: its finished record at its revision `c₁` (`cmpOk_fin`: the
compaction revision unchanged). -/
theorem sess_fin (γ : StoreNames) (L : Log) (hb : LogB L) (hL : 0 < L.length) (m : Bucket)
    (fin sched : Option w64) (X : backend.VData) (c₁ : Int) (p : Rev) (f : w64) (hf : W64 c₁ = f) :
    sessTrk (GF := GF) γ L m ⟨fin, sched⟩ X (c₁, p) ∗ cmpLb γ c₁ ⊢
      sessTrk γ L m ⟨some f, sched⟩ X (c₁, p) := by
  unfold sessTrk cmpLb
  cases hk : γ.kb with
  | none => simp only; iintro -; itrivial
  | some d =>
  by_cases hc : d.cm = true
  rotate_left
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; iintro -; itrivial
  simp only [hc, ↓reduceIte]
  iintro ⟨⟨Hr, Hl, Hj, %Hok⟩, -, %h1⟩
  obtain ⟨hok, hcr⟩ := snap.cmpOk_fin hb hL Hok h1
  simp only [hf] at hok hcr
  rw [hcr]
  iframe Hr Hl Hj
  ipureintro; exact hok

/-- **A batch's session closes**: the cursor's ghost at the job's, its halves the lock's tracked
compaction's and the job's. -/
theorem sess_close (γ : StoreNames) (L : Log) (m : Bucket) (rc : CmpRecs) (X : backend.VData)
    (jc : Int × Rev) :
    ⊢ sessTrk (GF := GF) γ L m rc X jc ==∗ cmpRest γ L m rc X ∗ jobCur γ jc := by
  unfold sessTrk cmpRest jobCur
  cases hk : γ.kb with
  | none => simp only; iintro -; imodintro; isplitl <;> itrivial
  | some d =>
  by_cases hc : d.cm = true
  rotate_left
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; iintro -; imodintro; isplitl <;> itrivial
  simp only [hc, ↓reduceIte]
  iintro ⟨Hr, Hl, ⟨%jg, Hj⟩, %Hok⟩
  imod ghostVar_update jc γ.jc jg $$ Hj with Hj
  icases ghostVar_halves γ.jc jc $$ Hj with ⟨Hj1, Hj2⟩
  imodintro
  iframe Hr Hl
  isplitl [Hj1]
  · iexists jc; iframe Hj1; ipureintro; exact Hok
  iexact Hj2

end sess

end mvcc
end EtcdGrove
end Perennial
