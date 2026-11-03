/-
**The compaction job keeps the tracking** (F2, stage 2, `notes/image-cmp-f2-plan.md`). Lean-first
(no Rocq counterpart).

The job (`store.scheduleCompaction`) deletes, batch by batch, the entries of the `Key` bucket
compaction at its revision `c` deletes, in key order (the revisions' order), and at its last batch
writes the finished record. The tracking's facts (`cmpFacts`) follow it with the job's cursor
(`d.ties.jg`, at `(c, cur)`: every entry below `cur` that compaction at `c` deletes is gone):

* `cmpFacts_start`: the job's first session sets the cursor to `(c, (0, 0))` (the records at or
  above `c`, `kbCrevLb`; nothing below `(0, 0)`);
* `cmpFacts_batch`: a batch's deletes (`D`, the deletable keys the batch read) move the cursor to
  `cur'`, the entries of the window `[cur, cur')` the bucket held being the batch's;
* `cmpFacts_fin`: the finished record at `c` keeps the records' revision.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CmpTrack

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- An entry's key in the bucket. -/
abbrev entKey (e : KvEnt) : GoString := revBytes e.rev e.tomb

/-- The lookup after inserting the entries of `l` whose key `g` keeps. -/
theorem lookup_foldl_insert_filter (l : List (GoString × GoString)) (g : GoString → Bool)
    (m : Bucket) (k : GoString) :
    ((l.filter fun p => g p.1).foldl (fun m p => GMap.insert p.1 p.2 m) m).lookup k =
      if g k then (l.foldl (fun m p => GMap.insert p.1 p.2 m) m).lookup k else m.lookup k := by
  induction l generalizing m with
  | nil => simp
  | cons p l ih =>
    rw [List.filter_cons, List.foldl_cons]
    by_cases hp : g p.1 = true
    · simp only [hp, ↓reduceIte, List.foldl_cons]
      rw [ih]
      by_cases hk : g k = true
      · simp only [hk, ↓reduceIte]
      · simp only [hk, Bool.false_eq_true, ↓reduceIte]
        have hne : p.1 ≠ k := fun h => hk (h ▸ hp)
        exact GMap.lookup_insert_ne _ _ hne
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      by_cases hk : g k = true
      · simp only [hk, ↓reduceIte]
        have hne : p.1 ≠ k := fun h => hp (h ▸ hk)
        rw [lookup_foldl_insert, lookup_foldl_insert]
        split
        · rfl
        · exact (GMap.lookup_insert_ne _ _ hne).symm
      · simp only [hk, Bool.false_eq_true, ↓reduceIte]

/-- The bucket of the entries whose key `g` keeps. -/
theorem bucketOfEnts_filter_lookup (ents : List KvEnt) (g : GoString → Bool) (k : GoString) :
    (bucketOfEnts (ents.filter fun e => g (entKey e))).lookup k =
      if g k then (bucketOfEnts ents).lookup k else none := by
  unfold bucketOfEnts
  have hm : (ents.filter fun e => g (entKey e)).map KvEnt.pair =
      (ents.map KvEnt.pair).filter (fun p => g p.1) := by
    rw [List.filter_map]; rfl
  rw [hm, lookup_foldl_insert_filter]
  rfl

/-- An entry's key is in the bucket of the entries. -/
theorem bucketOfEnts_mem (ents : List KvEnt) (e : KvEnt) (he : e ∈ ents) :
    (bucketOfEnts ents).lookup (entKey e) ≠ none := by
  unfold bucketOfEnts
  rw [lookup_foldl_insert]
  cases h : ((ents.map KvEnt.pair).reverse.find? fun p => decide (p.1 = entKey e)) with
  | some q => simp
  | none =>
    exfalso
    rw [List.find?_eq_none] at h
    exact h e.pair (List.mem_reverse.2 (List.mem_map.2 ⟨e, he, rfl⟩)) (by simp [KvEnt.pair])

theorem Rev.lt_trans' {a b c : Rev} (h1 : Rev.lt a b) (h2 : Rev.lt b c) : Rev.lt a c := by
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (by omega)
  · rw [h2] at h1; exact Or.inl h1
  · exact Or.inl (by rw [h1]; exact h2)
  · exact Or.inr ⟨h1.trans h2, by omega⟩

/-- The records' revision, when a revision, is one of the log's. -/
theorem recsOk_crev_lt0 {L : Log} {r : CmpRecs} (h : recsOk L r) (h0 : 0 ≤ r.crev) :
    r.crev < L.length := by
  by_cases hL : 1 ≤ L.length
  · exact recsOk_crev_lt1 L r h hL
  · exfalso
    have hf : r.fin = none := by
      cases hx : r.fin with
      | none => rfl
      | some x => have := h.1 x hx; omega
    have hs : r.sched = none := by
      cases hx : r.sched with
      | none => rfl
      | some x => have := h.2 x hx; omega
    have : r.crev = -1 := by
      unfold CmpRecs.crev CmpRecs.resumes CmpRecs.schedRev CmpRecs.finRev
      rw [hf, hs]; decide
    omega

/-- **The job's first session sets its cursor** to `(c, cur0)`, nothing of the log below `cur0`:
the records at or above `c` with the scheduled record their revision (`slOk`'s, once
`updateCompactRev` raised the bound to `c`). -/
theorem cmpFacts_start {L : Log} {r : CmpRecs} {vd : backend.VData} {v : backend.FkVals}
    {c0 : Int} {p0 : Rev} (c : Int) (cur0 : Rev) (hf : cmpFacts L r vd v c0 p0) (hc : c ≤ r.crev)
    (hs : r.schedRev = r.crev)
    (hb0 : ∀ e ∈ logEnts L 0 L.length, ¬ Rev.lt e.rev cur0) :
    cmpFacts L r vd v c cur0 := by
  obtain ⟨hcut, hv, -, -, -, hb, hwf⟩ := hf
  exact ⟨hcut, hv, hc, fun _ => hs, fun e he _ hlt => absurd hlt (hb0 e he), hb, hwf⟩

/-- No entry of the log is below `(0, 0)`. -/
theorem logEnts_not_lt_zero {L : Log} (hb : LogB L) :
    ∀ e ∈ logEnts L 0 L.length, ¬ Rev.lt e.rev ⟨W64 0, W64 0⟩ := by
  intro e he hlt
  have := logEnts_bounds L hb.1 hb.2 0 L.length (Nat.le_refl _) e he
  have hz : sint.Z (W64 0 : w64) = 0 := by decide
  rcases hlt with h | ⟨-, h⟩ <;> (simp only at h; omega)

/-- **A batch of the job keeps the facts**, its cursor moved from `cur` to `cur'`: the batch
deletes (`vd'` is `vd0` without them) keys `D` that compaction at `c` deletes, of entries below
`cur'`, and every deletable entry of the window `[cur, cur')` the bucket held is one of them. -/
theorem cmpFacts_batch {L : Log} {r : CmpRecs} {vd0 vd' : backend.VData} {v : backend.FkVals}
    {c : Int} {cur cur' : Rev} (D : GoString → Bool) (hf : cmpFacts L r vd0 v c cur)
    (hD : ∀ k, D k = true → KeyDel L c k)
    (hDr : ∀ e ∈ logEnts L 0 L.length, D (entKey e) = true → Rev.lt e.rev cur')
    (hv' : ∀ k, vd'.lookup (keyName, k) = if D k then none else vd0.lookup (keyName, k))
    (hwin : ∀ e ∈ logEnts L 0 L.length, KeyDel L c (entKey e) → ¬ Rev.lt e.rev cur →
      Rev.lt e.rev cur' → vd0.lookup (keyName, entKey e) ≠ none → D (entKey e) = true) :
    cmpFacts L r vd' v c cur' := by
  obtain ⟨⟨ents, hk, hok, hpos, hcut⟩, hv, hcc, hsc, hcd, hb, hwf⟩ := hf
  have hcd' : cursorDone L c cur' vd' := by
    intro e he hd hlt
    rw [hv']
    cases hDe : D (entKey e) with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hlc : Rev.lt e.rev cur
      · exact hcd e he hd hlc
      · apply Classical.byContradiction; intro hne
        have := hwin e he hd hlc hlt hne
        rw [hDe] at this; cases this
  let ents' := ents.filter fun e => !(D (entKey e))
  have hk' : keyOfView vd' (bucketOfEnts ents') := by
    intro k
    rw [hv', bucketOfEnts_filter_lookup ents (fun k => !(D k)) k]
    cases D k <;> simp [hk k]
  -- a deleted key's compaction is at a revision of the log
  have hDc : ∀ k, D k = true → 0 ≤ c ∧ c < L.length := by
    intro k h
    obtain ⟨hcl, r', t, -, h0, h1, -⟩ := hD k h
    exact ⟨by omega, hcl⟩
  refine ⟨⟨ents', hk', hok, hpos, ?_⟩, hv, hcc, hsc, hcd', hb, hwf⟩
  refine ⟨List.filter_sublist.trans hcut.1, fun e he hn => ?_, fun e₁ h₁ e₂ h₂ hke hlt hn => ?_⟩
  · by_cases hin : e ∈ ents
    · have hDe : D (entKey e) = true := by
        apply Classical.byContradiction; intro hDe
        exact hn (List.mem_filter.2 ⟨hin, by simpa using hDe⟩)
      obtain ⟨hc0, -⟩ := hDc _ hDe
      have hcr : r.crev < L.length := recsOk_crev_lt0 hok (by omega)
      exact KeyDel_mono hb (by omega) hcc hcr (hD _ hDe)
    · exact hcut.2.1 e he hin
  · intro h₁'
    obtain ⟨h₁e, -⟩ := List.mem_filter.1 h₁'
    by_cases hin₂ : e₂ ∈ ents
    · have hD₂ : D (entKey e₂) = true := by
        apply Classical.byContradiction; intro hDe
        exact hn (List.mem_filter.2 ⟨hin₂, by simpa using hDe⟩)
      have hd₁ := KeyDel_down hb hwf h₁ h₂ hke hlt (hD _ hD₂)
      have hlt₁ := Rev.lt_trans' hlt (hDr e₂ h₂ hD₂)
      have hnone := hcd' e₁ h₁ hd₁ hlt₁
      have hsome := bucketOfEnts_mem ents' e₁ h₁'
      rw [← hk'] at hsome
      exact hsome hnone
    · exact hcut.2.2 e₁ h₁ e₂ h₂ hke hlt hin₂ h₁e

/-- **The finished record at the job's revision keeps the records' revision** (the job's last
batch): with the records at or above `c` (`c ≥ 1`) and the scheduled record their revision. -/
theorem cmpFacts_fin {L : Log} {r : CmpRecs} {vd : backend.VData} {v : backend.FkVals} {p : Rev}
    (rev : w64) (hf : cmpFacts L r vd v (sint.Z rev) p) (h1 : 1 ≤ sint.Z rev)
    (hle : sint.Z rev ≤ r.crev) (hs : r.schedRev = r.crev) :
    cmpFacts L { r with fin := some rev } vd
        (fkSet finKeyBytes (revBytes ⟨rev, W64 0⟩ false) v) (sint.Z rev) p ∧
      ({ r with fin := some rev } : CmpRecs).crev = r.crev ∧
      ({ r with fin := some rev } : CmpRecs).schedRev = r.schedRev := by
  obtain ⟨⟨ents, hk, hok, hpos, hcut⟩, hv, hcc, -, hcd, hb, hwf⟩ := hf
  have hs' : ({ r with fin := some rev } : CmpRecs).schedRev = r.schedRev := rfl
  have hf' : ({ r with fin := some rev } : CmpRecs).finRev = sint.Z rev := rfl
  have hres : ({ r with fin := some rev } : CmpRecs).resumes =
      decide (r.schedRev ≠ 0 ∧ sint.Z rev < r.schedRev) := rfl
  have hcr : ({ r with fin := some rev } : CmpRecs).crev = r.crev := by
    have e : ({ r with fin := some rev } : CmpRecs).crev =
        if decide (r.schedRev ≠ 0 ∧ sint.Z rev < r.schedRev) then r.schedRev else sint.Z rev := rfl
    rw [e]
    cases hd : decide (r.schedRev ≠ 0 ∧ sint.Z rev < r.schedRev)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hn := of_decide_eq_false hd
      by_cases h0 : r.schedRev = 0
      · omega
      · have : ¬ sint.Z rev < r.schedRev := fun h => hn ⟨h0, h⟩
        omega
    · simp only [↓reduceIte]; exact hs
  have hcrl : r.crev < L.length := recsOk_crev_lt0 hok (by omega)
  refine ⟨⟨⟨ents, hk, ⟨fun x hx => ?_, hok.2⟩, ⟨fun x hx => ?_, hpos.2⟩, ?_⟩, ?_, ?_, ?_, hcd,
    hb, hwf⟩, hcr, hs'⟩
  · simp only [Option.some.injEq] at hx; subst hx; exact ⟨by omega, by omega⟩
  · simp only [Option.some.injEq] at hx; subst hx; exact h1
  · rw [hcr]; exact hcut
  · unfold fkSet; rw [if_pos rfl, hv]; rfl
  · rw [hcr]; exact hcc
  · intro _; rw [hcr, hs', hs]

/-- A string is below its extensions. -/
theorem goStringLt_prefix (p : GoString) (x : w8) (xs : GoString) : go.GoStringLt p (p ++ x :: xs) := by
  induction p with
  | nil => exact go.goStringLt_nil_cons x xs
  | cons a p ih => exact List.Lex.cons ih

/-- `Rev.lt` of revisions of non-negative parts orders their keys. -/
theorem revBytes_lt_of_lt {a b : Rev} (ha : 0 ≤ sint.Z a.main ∧ 0 ≤ sint.Z a.sub)
    (hb : 0 ≤ sint.Z b.main ∧ 0 ≤ sint.Z b.sub) (h : Rev.lt a b) (t t' : Bool) :
    go.GoStringLt (revBytes a t) (revBytes b t') := by
  apply RevOrder.revBytes_lt
  have e1 : uint.Z a.main = sint.Z a.main := by word
  have e2 : uint.Z b.main = sint.Z b.main := by word
  have e3 : uint.Z a.sub = sint.Z a.sub := by word
  have e4 : uint.Z b.sub = sint.Z b.sub := by word
  rcases h with h | ⟨h, h'⟩
  · left; omega
  · right; exact ⟨h, by omega⟩

/-- A key at or below another's: its revision is not above. -/
theorem not_lt_of_key_le {a b : Rev} (ha : 0 ≤ sint.Z a.main ∧ 0 ≤ sint.Z a.sub)
    (hb : 0 ≤ sint.Z b.main ∧ 0 ≤ sint.Z b.sub) {t t' : Bool}
    (h : go.GoStringLe (revBytes a t) (revBytes b t')) : ¬ Rev.lt b a := by
  intro hlt
  have h2 := revBytes_lt_of_lt hb ha hlt t' t
  rcases h with h | h
  · rw [h] at h2; exact go.goStringLt_irrefl _ h2
  · exact go.goStringLt_asymm h h2

/-- The key of a revision at or above `cur` is at or above `cur`'s key. -/
theorem key_ge_of_not_lt {a cur : Rev} (ha : 0 ≤ sint.Z a.main ∧ 0 ≤ sint.Z a.sub)
    (hc : 0 ≤ sint.Z cur.main ∧ 0 ≤ sint.Z cur.sub) (h : ¬ Rev.lt a cur) (t : Bool) :
    go.GoStringLe (revBytes cur false) (revBytes a t) := by
  by_cases he : a = cur
  · subst he
    cases t
    · exact Or.inl rfl
    · right
      unfold revBytes
      simp only [↓reduceIte, Bool.false_eq_true, List.append_nil]
      exact goStringLt_prefix (u64Be a.main ++ [W8 95] ++ u64Be a.sub) (W8 116) []
  · right
    apply revBytes_lt_of_lt hc ha _ false t
    unfold Rev.lt at h ⊢
    have hm : a.main = cur.main → a.sub ≠ cur.sub := fun h1 h2 => he (by cases a; cases cur; simp_all)
    have e1 : a.main = cur.main ↔ sint.Z a.main = sint.Z cur.main :=
      ⟨fun h => by rw [h], fun h => by word⟩
    have e2 : a.sub = cur.sub ↔ sint.Z a.sub = sint.Z cur.sub :=
      ⟨fun h => by rw [h], fun h => by word⟩
    by_cases h1 : sint.Z cur.main < sint.Z a.main
    · exact Or.inl h1
    · right
      have hmm : sint.Z a.main = sint.Z cur.main := by
        apply Classical.byContradiction; intro hne
        exact h (Or.inl (by omega))
      refine ⟨(e1.2 hmm).symm, ?_⟩
      have hs := hm (e1.2 hmm)
      have : sint.Z a.sub ≠ sint.Z cur.sub := fun h' => hs (e2.2 h')
      have : ¬ sint.Z a.sub < sint.Z cur.sub := fun h' => h (Or.inr ⟨e1.2 hmm, h'⟩)
      omega

/-- `bs` is at or below every key of a revision of non-negative parts (the job's first `last`,
zero bytes). -/
def keyFloor (bs : GoString) : Prop :=
  ∀ (r : Rev) (t : Bool), 0 ≤ sint.Z r.main → 0 ≤ sint.Z r.sub → go.GoStringLe bs (revBytes r t)

/-- **A batch of the job at `c`, from the key `bs`** (pure; the store's bucket `p0` at the
session's start, `p'` after its deletes): the batch deletes keys `D` compaction at `c` deletes, of
entries below the new cursor `cur'`, and every deletable entry at or above `bs` and below `cur'`
the bucket held. -/
def batchOk (L : Log) (c : Int) (bs : GoString) (p0 p' : Bucket) (cur' : Rev) : Prop :=
  ∃ D : GoString → Bool, (∀ k, D k = true → KeyDel L c k) ∧
    (∀ e ∈ logEnts L 0 L.length, D (entKey e) = true → Rev.lt e.rev cur') ∧
    (∀ k, p'.lookup k = if D k then none else p0.lookup k) ∧
    (∀ e ∈ logEnts L 0 L.length, KeyDel L c (entKey e) → go.GoStringLe bs (entKey e) →
      Rev.lt e.rev cur' → p0.lookup (entKey e) ≠ none → D (entKey e) = true)

/-- The physical view's keys are its entries' keys. -/
theorem keys_of_cut {L : Log} {r : CmpRecs} {vd0 : backend.VData} {v : backend.FkVals} {c : Int}
    {cur : Rev} {p0 : Bucket} (hf : cmpFacts L r vd0 v c cur) (hk0 : keyOfView vd0 p0) :
    ∀ k x, p0.lookup k = some x → ∃ e ∈ logEnts L 0 L.length, entKey e = k := by
  intro k x hx
  obtain ⟨⟨ents, hk, -, -, hcut⟩, -⟩ := hf
  rw [← hk0, hk] at hx
  unfold bucketOfEnts at hx
  rw [lookup_foldl_insert] at hx
  cases h : ((ents.map KvEnt.pair).reverse.find? fun p => decide (p.1 = k)) with
  | none => rw [h] at hx; cases hx
  | some q =>
    have hq := List.mem_reverse.1 (List.mem_of_find?_eq_some h)
    have hqk : q.1 = k := by simpa using List.find?_some h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hq
    exact ⟨e, hcut.1.subset he, hqk⟩

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The job's cursor between its batches** (the job's half of `d.ties.jg`, in compaction mode):
either the next batch starts below every key (`keyFloor`: the first, whatever the cursor), or the
cursor is the job's, at `c`, at the revision whose key is `bs`. -/
def jobCurAt (kb : Option KBReal) (c : Int) (bs : GoString) : IProp GF :=
  match kb with
  | none => iprop(True)
  | some d =>
    if d.cm then iprop(∃ (c' : Int) (p : Rev), ghostVar d.ties.jg (1 : Qp).half (c', p.main, p.sub) ∗
      ⌜keyFloor bs ∨ (c' = c ∧ bs = revBytes p false ∧ 0 ≤ sint.Z p.main ∧ 0 ≤ sint.Z p.sub)⌝)
    else iprop(True)

theorem jobCurAt_start (kb : Option KBReal) (c : Int) (bs : GoString) (h : keyFloor bs) :
    kbJob (GF := GF) kb ⊢ jobCurAt kb c bs := by
  unfold kbJob jobCurAt
  cases kb with
  | none => exact .rfl
  | some d =>
    simp only
    cases d.cm
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact .rfl
    · simp only [↓reduceIte]
      iintro ⟨%c', %p, H⟩
      iexists c', p
      iframe H
      ipureintro; exact Or.inl h

theorem jobCurAt_kbJob (kb : Option KBReal) (c : Int) (bs : GoString) :
    jobCurAt (GF := GF) kb c bs ⊢ kbJob kb := by
  unfold kbJob jobCurAt
  cases kb with
  | none => exact .rfl
  | some d =>
    simp only
    cases d.cm
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact .rfl
    · simp only [↓reduceIte]
      iintro ⟨%c', %p, H, -⟩
      iexists c', p
      iexact H

/-- **The job's session, opened** (in compaction mode): the tracking's records (at or above `c`,
`kbCrevLb`), the cursor (both halves) at `(c, cur)`, the client's half of the compaction keys'
values, and the facts, the client's half of the physical view lent out at its `Key` bucket `p0`. -/
def jobSess (kb : Option KBReal) (L : Log) (c : Int) (bs : GoString) (p0 : Bucket) : IProp GF :=
  match kb with
  | none => iprop(True)
  | some d =>
    if d.cm then
      iprop(∃ (vd0 : backend.VData) (v : backend.FkVals) (r : CmpRecs) (cur : Rev) (n : Nat),
        backend.ckHalf d.γB v ∗ ghostVar d.ties.lg (1 : Qp).half L ∗
        ghostVar d.ties.sg (1 : Qp).half r.crev ∗
        ghostVar d.ties.jg (1 : Qp).half (c, cur.main, cur.sub) ∗
        ghostVar d.ties.jg (1 : Qp).half (c, cur.main, cur.sub) ∗ monoNatAuthOwn d.ties.sl 1 n ∗
        ⌜slOk n r ∧ cmpFacts L r vd0 v c cur ∧ keyOfView vd0 p0 ∧ c ≤ r.crev ∧
          r.schedRev = r.crev ∧ 1 ≤ c ∧
          ∀ e ∈ logEnts L 0 L.length, ¬ Rev.lt e.rev cur → go.GoStringLe bs (entKey e)⌝)
    else iprop(True)

/-- **The job opens its session** (its batch's lock held): from the tracking, its cursor and the
records' lower bound at `c`, the client's half of the physical view at some bucket `p0`. -/
theorem jobSess_open (γ : StoreNames) (L : Log) (c : Int) (bs : GoString) (h : kbCmpM γ.kb)
    (h1 : 1 ≤ c) :
    kbTrack (GF := GF) γ.kb L ∗ jobCurAt γ.kb c bs ∗ kbCrevLb γ.kb c ⊢
      |==> ∃ p0 : Bucket, storePV γ p0 ∗ jobSess γ.kb L c bs p0 := by
  unfold storePV
  generalize γ.kb = kb at h ⊢
  cases kb with
  | none =>
    iintro -
    imodintro
    iexists GMap.empty
    unfold jobSess
    isplitl <;> itrivial
  | some d =>
    have hcm : d.cm = true := h
    unfold kbTrack cmpTrack cmpTrackOn jobCurAt kbCrevLb jobSess bkPV
    simp only [hcm, ↓reduceIte]
    iintro ⟨⟨%vd, %v, Hp, Hc, %r, %ct, %pt, %n, Hl, Hs, Hj, Hn, %hn, %hf⟩, ⟨%c', %p, Hj', %hcur⟩,
      #Hlb⟩
    ihave %hle := monoNatLbOwn_valid d.ties.sl 1 n (crevN c) $$ Hn Hlb
    ihave %hj := ghostVar_agree d.ties.jg _ _ _ _ $$ Hj Hj'
    have hfc := hf
    obtain ⟨⟨ents, -, hok, -, -⟩, -, -, -, -, hb, -⟩ := hfc
    have hge : -1 ≤ r.crev := recsOk_crev_ge L r hok
    have hcr : c ≤ r.crev := crevN_le (by omega) hge (Nat.le_trans hle.2 hn.1)
    have hsc : r.schedRev = r.crev := hn.2 (by unfold crevN at hle; omega)
    have hbnd := logEnts_bounds L hb.1 hb.2 0 L.length (Nat.le_refl _)
    rcases hcur with hfl | ⟨rfl, rfl, hp0, hp1⟩
    · imod ghostVar_update_halves ((c, W64 0, W64 0) : Int × w64 × w64) d.ties.jg _ _ $$ Hj Hj'
        with ⟨Hj, Hj'⟩
      imodintro
      iexists keyBucket vd
      isplitl [Hp]
      · iexists vd; iframe Hp; ipureintro; exact keyOfView_keyBucket vd
      iexists vd, v, r, ⟨W64 0, W64 0⟩, n
      iframe Hc Hl Hs Hj Hj' Hn
      ipureintro
      refine ⟨hn, cmpFacts_start c _ hf hcr hsc (logEnts_not_lt_zero hb), keyOfView_keyBucket vd,
        hcr, hsc, h1, fun e he _ => ?_⟩
      exact hfl e.rev e.tomb (hbnd e he).1 (hbnd e he).2
    · simp only [Prod.mk.injEq] at hj
      obtain ⟨rfl, hm, hs⟩ := hj
      have hpt : pt = p := by cases pt; cases p; simp_all
      subst hpt
      imodintro
      iexists keyBucket vd
      isplitl [Hp]
      · iexists vd; iframe Hp; ipureintro; exact keyOfView_keyBucket vd
      iexists vd, v, r, pt, n
      iframe Hc Hl Hs Hj Hj' Hn
      ipureintro
      refine ⟨hn, hf, keyOfView_keyBucket vd, hcr, hsc, h1, fun e he hlt => ?_⟩
      exact key_ge_of_not_lt (hbnd e he) ⟨hp0, hp1⟩ hlt e.tomb

/-- The session's facts after a batch: the cut at the new cursor (`cmpFacts_batch`). -/
theorem jobSess_batch_facts {L : Log} {r : CmpRecs} {vd0 vd' : backend.VData} {v : backend.FkVals}
    {c : Int} {cur cur' : Rev} {bs : GoString} {p0 p' : Bucket}
    (hf : cmpFacts L r vd0 v c cur) (hk0 : keyOfView vd0 p0) (hk' : keyOfView vd' p')
    (hbs : ∀ e ∈ logEnts L 0 L.length, ¬ Rev.lt e.rev cur → go.GoStringLe bs (entKey e))
    (hb : batchOk L c bs p0 p' cur') : cmpFacts L r vd' v c cur' := by
  obtain ⟨D, hD, hDr, hp', hwin⟩ := hb
  refine cmpFacts_batch D hf hD hDr (fun k => ?_) (fun e he hd hlt hlt' hne => ?_)
  · rw [hk' k, hp' k, hk0 k]
  · exact hwin e he hd (hbs e he hlt) hlt' (by rw [← hk0]; exact hne)

/-- **The job closes a batch's session** (not the last): the tracking at the new cursor `cur'`
(both halves), whose key the next batch starts from. -/
theorem jobSess_close (γ : StoreNames) (L : Log) (c : Int) (bs : GoString) (p0 p' : Bucket)
    (cur' : Rev) (h : kbCmpM γ.kb)
    (hb : (∀ k x, p0.lookup k = some x → ∃ e ∈ logEnts L 0 L.length, entKey e = k) →
      storePVx γ → c < L.length → batchOk L c bs p0 p' cur')
    (hc' : 0 ≤ sint.Z cur'.main ∧ 0 ≤ sint.Z cur'.sub) :
    jobSess (GF := GF) γ.kb L c bs p0 ∗ storePV γ p' ==∗
      kbTrack γ.kb L ∗ jobCurAt γ.kb c (revBytes cur' false) := by
  unfold storePV
  unfold storePVx at hb
  generalize γ.kb = kb at h hb ⊢
  cases kb with
  | none =>
    iintro -
    imodintro
    unfold kbTrack jobCurAt
    isplitl <;> itrivial
  | some d =>
    have hcm : d.cm = true := h
    unfold kbTrack cmpTrack cmpTrackOn jobCurAt jobSess bkPV
    simp only [hcm, ↓reduceIte]
    iintro ⟨⟨%vd0, %v, %r, %cur, %n, Hc, Hl, Hs, Hj, Hj', Hn, %hs⟩, %vd', Hp, %hk'⟩
    obtain ⟨hn, hf, hk0, hcr, -, h1, hbs⟩ := hs
    have hcl : c < L.length := by
      have := recsOk_crev_lt0 hf.1.choose_spec.2.1 (by omega)
      omega
    have hf' := jobSess_batch_facts hf hk0 hk' hbs (hb (keys_of_cut hf hk0) rfl hcl)
    imod ghostVar_update_halves ((c, cur'.main, cur'.sub) : Int × w64 × w64) d.ties.jg _ _ $$ Hj Hj'
      with ⟨Hj, Hj'⟩
    imodintro
    isplitl [Hp Hc Hl Hs Hj Hn]
    · iexists vd', v
      iframe Hp Hc
      iexists r, c, cur', n
      iframe Hl Hs Hj Hn
      ipureintro; exact ⟨hn, hf'⟩
    iexists c, cur'
    iframe Hj'
    ipureintro; exact Or.inr ⟨rfl, rfl, hc'⟩

/-- **The job's last batch closes its session** with the finished record at `rev`: the client's
half of the compaction keys' values lent to the record's put, and then the tracking (the records
keep their revision, `cmpFacts_fin`) and the job's cursor. -/
theorem jobSess_fin (γ : StoreNames) (L : Log) (rev : w64) (bs : GoString) (p0 p' : Bucket)
    (cur' : Rev) (h : kbCmpM γ.kb)
    (hb : (∀ k x, p0.lookup k = some x → ∃ e ∈ logEnts L 0 L.length, entKey e = k) →
      storePVx γ → sint.Z rev < L.length → batchOk L (sint.Z rev) bs p0 p' cur') :
    jobSess (GF := GF) γ.kb L (sint.Z rev) bs p0 ∗ storePV γ p' ⊢
      ∃ cv : backend.FkVals, storeCK γ cv ∗
        (storeCK γ (fkSet finKeyBytes (revBytes ⟨rev, W64 0⟩ false) cv) ==∗
          kbTrack γ.kb L ∗ kbJob γ.kb) := by
  unfold storePV storeCK
  unfold storePVx at hb
  generalize γ.kb = kb at h hb ⊢
  cases kb with
  | none =>
    iintro -
    iexists (none, none)
    isplitr; · itrivial
    iintro -
    imodintro
    unfold kbTrack kbJob
    isplitl <;> itrivial
  | some d =>
    have hcm : d.cm = true := h
    unfold kbTrack cmpTrack cmpTrackOn kbJob jobSess bkPV
    simp only [hcm, ↓reduceIte]
    iintro ⟨⟨%vd0, %v, %r, %cur, %n, Hc, Hl, Hs, Hj, Hj', Hn, %hs⟩, %vd', Hp, %hk'⟩
    obtain ⟨hn, hf, hk0, hcr, hsc, h1, hbs⟩ := hs
    have hcl : sint.Z rev < L.length := by
      have := recsOk_crev_lt0 hf.1.choose_spec.2.1 (by omega)
      omega
    have hf' := jobSess_batch_facts hf hk0 hk' hbs (hb (keys_of_cut hf hk0) rfl hcl)
    obtain ⟨hf'', hcr', hsc'⟩ := cmpFacts_fin rev hf' h1 hcr hsc
    iexists v
    iframe Hc
    iintro Hc
    imod ghostVar_update_halves ((sint.Z rev, cur'.main, cur'.sub) : Int × w64 × w64) d.ties.jg _ _
      $$ Hj Hj' with ⟨Hj, Hj'⟩
    imodintro
    isplitl [Hp Hc Hl Hs Hj Hn]
    · iexists vd', fkSet finKeyBytes (revBytes ⟨rev, W64 0⟩ false) v
      iframe Hp Hc
      iexists { r with fin := some rev }, sint.Z rev, cur', n
      rw [hcr']
      iframe Hl Hs Hj Hn
      ipureintro
      refine ⟨⟨by rw [hcr']; exact hn.1, fun h => by rw [hsc', hcr']; exact hn.2 h⟩, hf''⟩
    iexists sint.Z rev, cur'
    iexact Hj'

end proof

end mvcc
end EtcdGrove
end Perennial
