/-
**`restore()` over a bucket a compaction thinned** (M2, the storage side, item 18: the inner
`store.restore` in compaction mode; pure). The image's `Key` entries `ents` are the log's but for a
prefix per key deletable at the restored revision (`entsCutAt`, `InvIndexRestore.lean`): a sublist of
the log's entries. What `restore()`'s chunk loop and its `currentRev` read of them:

- `bucketOfEnts ents`, the bucket of the entries, looked up as the entries say
  (`bucketOfEnts_lookup_iff`), and its range from a revision on (`bucketRange_fromE`), chunk after
  chunk (`entsFromE_next`), as `RestoreChunks.lean` for the whole bucket;
- **the restored `currentRev`** (`restoreCur_cut`): the rebuild answers the last surviving entry's
  revision, which `restore()` raises to the finished and then the scheduled record
  (`kvstore.go:367-386`); over the job's shape the result is the log's last revision, whether or not
  the compaction deleted that revision's entries (then it is at or below the restored revision,
  the records' maximum).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndexRestore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CmpRecs

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

section pure
variable [GooseExts]

/-- The `Key` bucket of the entries `ents` (`bucketMap`'s fold over them). -/
def bucketOfEnts (ents : List KvEnt) : Bucket :=
  (ents.map KvEnt.pair).foldl (fun m p => GMap.insert p.1 p.2 m) GMap.empty

/-- The whole bucket's entries make the log's bucket. -/
theorem bucketOfEnts_logEnts (L : Log) :
    bucketOfEnts (logEnts L 0 L.length) = bucketMap L := by
  unfold bucketOfEnts bucketMap; rw [bucketOf_logEnts]

/-- **The bucket of a sublist of a log's entries** is looked up as the entries say. -/
theorem bucketOfEnts_lookup_iff (L : Log) (hb : LogB L) {ents : List KvEnt}
    (hs : ents.Sublist (logEnts L 0 L.length)) (k v : GoString) :
    bucketOfEnts ents !! k = some v ↔ (k, v) ∈ ents.map KvEnt.pair := by
  have hsub : ∀ p ∈ ents.map KvEnt.pair, p ∈ bucketOf L := by
    intro p hp
    rw [bucketOf_logEnts]
    exact (hs.map KvEnt.pair).subset hp
  constructor
  · intro h
    change (bucketOfEnts ents).lookup k = some v at h
    unfold bucketOfEnts at h
    rw [lookup_foldl_insert] at h
    cases hf : (ents.map KvEnt.pair).reverse.find? (fun p => decide (p.1 = k)) with
    | none => rw [hf] at h; cases h
    | some p =>
      rw [hf] at h
      cases h
      have hp := List.mem_reverse.1 (List.mem_of_find?_eq_some hf)
      have hk : p.1 = k := by simpa using List.find?_some hf
      rw [← hk]; exact hp
  · intro h
    change (bucketOfEnts ents).lookup k = some v
    unfold bucketOfEnts
    rw [lookup_foldl_insert]
    cases hf : (ents.map KvEnt.pair).reverse.find? (fun p => decide (p.1 = k)) with
    | none =>
      exfalso
      rw [List.find?_eq_none] at hf
      exact hf (k, v) (List.mem_reverse.2 h) (by simp)
    | some p =>
      have hp := List.mem_reverse.1 (List.mem_of_find?_eq_some hf)
      have hk : p.1 = k := by simpa using List.find?_some hf
      simp only
      rw [bucketOf_fun L hb.1 hb.2 p (hsub p hp) (k, v) (hsub _ h) hk]

/-- The entries `ents` from the revision `r` on. -/
def entsFromE (ents : List KvEnt) (r : Rev) : List KvEnt :=
  ents.filter fun e => decide (revLeN r e.rev)

/-- **The range `restore` reads from the revision `r`** of the bucket of a sublist of a log's
entries: those entries from `r` on, in revision order. -/
theorem bucketRange_fromE (L : Log) (hb : LogB L) {ents : List KvEnt}
    (hs : ents.Sublist (logEnts L 0 L.length)) (r : Rev) :
    bucketRange (bucketOfEnts ents) (revBytes r false) (revBytes revMax false) =
      (entsFromE ents r).map KvEnt.pair := by
  rw [bucketRange_eq_iff]
  constructor
  · rw [List.map_map, List.pairwise_map]
    exact (logEnts_keys_sorted L hb.1 hb.2 0 L.length).sublist (List.filter_sublist.trans hs)
  · intro k v
    rw [bucketOfEnts_lookup_iff L hb hs]
    simp only [entsFromE, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨e, ⟨he, hr⟩, hpe⟩
      simp only [KvEnt.pair, Prod.mk.injEq] at hpe
      obtain ⟨rfl, rfl⟩ := hpe
      exact ⟨⟨e, he, rfl⟩, (revBytes_le_iff r e.rev e.tomb).2 hr,
        logEnts_lt_max L hb.1 e (hs.subset he)⟩
    · rintro ⟨⟨e, he, hpe⟩, hk1, -⟩
      simp only [KvEnt.pair, Prod.mk.injEq] at hpe
      obtain ⟨rfl, rfl⟩ := hpe
      exact ⟨e, ⟨he, (revBytes_le_iff r e.rev e.tomb).1 hk1⟩, rfl⟩

/-- From revision `1` on, all of them (a log's entries are past revision `0`). -/
theorem entsFromE_one (L : Log) (hb : LogB L) (h0 : L.getD 0 [] = []) {ents : List KvEnt}
    (hs : ents.Sublist (logEnts L 0 L.length)) :
    entsFromE ents ⟨W64 1, W64 0⟩ = ents := by
  have hok := logEnts_restoreOk L hb.1 hb.2 h0
  apply List.filter_eq_self.2
  intro e he
  have h1 := (hok.2 e (hs.subset he)).1
  simp only [decide_eq_true_eq]
  unfold revLeN
  show (W64 1).toNat < e.rev.main.toNat ∨ (W64 1 = e.rev.main ∧ (W64 0).toNat ≤ e.rev.sub.toNat)
  rcases Nat.lt_or_ge 1 e.rev.main.toNat with h | h
  · left; exact h
  · right; constructor
    · apply BitVec.eq_of_toNat_eq; simp only [show (W64 1).toNat = 1 from rfl]; word
    · simp

/-- **The next chunk**: after a full chunk of `n` entries from `r`, whose last is `e`, the entries
from just after `e` are the rest. -/
theorem entsFromE_next (L : Log) (hb : LogB L) {ents : List KvEnt}
    (hs : ents.Sublist (logEnts L 0 L.length)) (r : Rev) (n : Nat) (hn : 0 < n) (e : KvEnt)
    (he : (entsFromE ents r)[n - 1]? = some e) :
    entsFromE ents (revNext e.rev) = (entsFromE ents r).drop n := by
  have hsE := (logEnts_codes_sorted L hb.1 hb.2 0 L.length).sublist hs
  have hsR : (entsFromE ents r).Pairwise (fun a b => revCode a.rev < revCode b.rev) :=
    hsE.sublist List.filter_sublist
  rw [drop_eq_filter_gt (fun e : KvEnt => revCode e.rev) hsR n hn e he]
  have hmem : e ∈ entsFromE ents r := List.mem_of_getElem? he
  have heE : e ∈ logEnts L 0 L.length := hs.subset (List.mem_filter.1 hmem).1
  have her : revLeN r e.rev := by simpa using (List.mem_filter.1 hmem).2
  rw [revLeN_iff] at her
  have hc := revCode_next e.rev (logEnts_sub_lt L hb.2 e heE)
  unfold entsFromE
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  simp only [revLeN_iff]
  rw [hc]
  by_cases h1 : revCode r ≤ revCode x.rev <;> by_cases h2 : revCode e.rev < revCode x.rev <;>
    simp [h1, h2] <;> omega

/-- **A sublist of a log's entries is what `restoreIntoIndex` takes.** -/
theorem restoreOk_sublist {l l' : List KvEnt} (h : RestoreEntsOk l) (hs : l'.Sublist l) :
    RestoreEntsOk l' :=
  ⟨h.1.sublist hs, fun e he => h.2 e (hs.subset he)⟩

/-- The restored log's first two revisions have no entry. -/
theorem logEnts_two : logEnts ([[], []] : Log) 0 2 = [] := by decide

/-- **A log's entries are of its revisions** `1 ≤ main ≤ |L| - 1`. -/
theorem logEnts_main_le (L : Log) (hb : LogB L) (e : KvEnt) (he : e ∈ logEnts L 0 L.length) :
    sint.Z e.rev.main ≤ (L.length : Int) - 1 := by
  obtain ⟨j, i, c, kv, -, -, hj, -, -, -, -, rfl⟩ := logEnts_entry L 0 L.length e he
  have hl := hb.1
  show sint.Z (W64 j) ≤ (L.length : Int) - 1
  have : sint.Z (W64 j) = j := by word
  omega

/-- The finished record as `restore()` stores it in `compactMainRev`. -/
theorem CmpRecs.finRev_getD (r : CmpRecs) :
    sint.Z (r.fin.getD (W64 (-1))) = r.finRev := by
  unfold CmpRecs.finRev
  cases hf : r.fin with
  | none => rfl
  | some x => rfl

/-- The scheduled record as `restore()` reads it. -/
theorem CmpRecs.schedRev_getD (r : CmpRecs) :
    sint.Z (r.sched.getD (W64 0)) = r.schedRev := by
  unfold CmpRecs.schedRev
  cases hf : r.sched with
  | none => rfl
  | some x => rfl

/-- The restored revision is one of the two records' (as `restore()` reads them). -/
theorem CmpRecs.crev_le_max (r : CmpRecs) : r.crev ≤ max r.finRev r.schedRev := by
  unfold CmpRecs.crev; split <;> omega

/-- The restored revision is `-1` or a record's. -/
theorem CmpRecs.crev_ge (L : Log) (r : CmpRecs) (h : recsOk L r) : -1 ≤ r.crev := by
  have hf : -1 ≤ r.finRev := by
    unfold CmpRecs.finRev
    cases hfin : r.fin with
    | none => simp
    | some x => have := (h.1 x hfin).1; simp; omega
  unfold CmpRecs.crev CmpRecs.resumes
  split
  · rename_i hr; simp only [decide_eq_true_eq] at hr; omega
  · exact hf

/-- The last element of a list sorted by `R` is `R`-above every other one. -/
theorem pairwise_getLast {α : Type} {R : α → α → Prop} {l : List α} (hs : l.Pairwise R) {x e : α}
    (hx : x ∈ l) (he : l.getLast? = some e) : x = e ∨ R x e := by
  rw [List.getLast?_eq_some_iff] at he
  obtain ⟨ys, rfl⟩ := he
  rw [List.pairwise_append] at hs
  rcases List.mem_append.1 hx with h | h
  · exact Or.inr (hs.2.2 x h e (by simp))
  · exact Or.inl (by simpa using h)

/-- **The restored `currentRev`** (`kvstore.go:367-386`): the rebuild's answer (the last surviving
entry's revision, `1` if none) raised to the finished record and then to the scheduled one is the
restored log's last revision, over the job's shape at the restored revision. -/
theorem restoreCur_cut (R : Log) (hR : ∀ cs ∈ R, cs ≠ []) (hRne : R ≠ [])
    (hb : LogB ([[], []] ++ R)) (r : CmpRecs) (hrec : recsOk ([[], []] ++ R) r)
    (ents : List KvEnt) (hcut : entsCutAt ([[], []] ++ R) r.crev ents) :
    max (max (sint.Z (restoreLastRev ents)) r.finRev) r.schedRev =
      (([[], []] ++ R).length : Int) - 1 := by
  obtain ⟨hsub, hdel, -⟩ := hcut
  have hlast := restoreLastRev_logEnts R hR (by have := hb.1; simp at this; omega)
  obtain ⟨L, hL⟩ : ∃ L, L = [[], []] ++ R := ⟨_, rfl⟩
  rw [← hL] at hb hrec hsub hdel hlast ⊢
  have hlen : 3 ≤ L.length := by
    rw [hL, List.length_append]
    have : 1 ≤ R.length := List.length_pos_iff.2 hRne
    simp; omega
  have hlen63 := hb.1
  have h0 : L.getD 0 [] = [] := by rw [hL]; rfl
  have hok := logEnts_restoreOk L hb.1 hb.2 h0
  -- the records are below the last revision
  have hfin : r.finRev ≤ (L.length : Int) - 1 := by
    unfold CmpRecs.finRev
    cases hf : r.fin with
    | none => simp; omega
    | some x => have := (hrec.1 x hf).2; simp; omega
  have hsch : r.schedRev ≤ (L.length : Int) - 1 := by
    unfold CmpRecs.schedRev
    cases hf : r.sched with
    | none => simp; omega
    | some x => have := (hrec.2 x hf).2; simp; omega
  -- the log's last entry is at its last revision
  have hL1 : sint.Z (W64 ((L.length : Int) - 1)) = (L.length : Int) - 1 := by word
  unfold restoreLastRev at hlast
  obtain ⟨estar, hestar⟩ : ∃ e, (logEnts L 0 L.length).getLast? = some e := by
    cases h : (logEnts L 0 L.length).getLast? with
    | none =>
      rw [h] at hlast
      simp only at hlast
      have := congrArg sint.Z hlast
      rw [hL1] at this
      simp only [show sint.Z (W64 1) = 1 from rfl] at this
      omega
    | some e => exact ⟨e, rfl⟩
  have hstar_main : sint.Z estar.rev.main = (L.length : Int) - 1 := by
    rw [hestar] at hlast
    simp only at hlast
    rw [hlast]; exact hL1
  have hstar_mem : estar ∈ logEnts L 0 L.length := List.mem_of_getLast? hestar
  -- the rebuild's answer is a revision of the log
  have hans : 1 ≤ sint.Z (restoreLastRev ents) ∧ sint.Z (restoreLastRev ents) ≤ (L.length : Int) - 1 := by
    unfold restoreLastRev
    cases h : ents.getLast? with
    | none => simp only [show sint.Z (W64 1) = 1 from rfl]; omega
    | some e =>
      simp only
      have he := hsub.subset (List.mem_of_getLast? h)
      exact ⟨(hok.2 e he).1, logEnts_main_le L hb e he⟩
  by_cases hin : estar ∈ ents
  · -- the last revision survives: the rebuild answers it
    have hsorted : ents.Pairwise (fun a b => Rev.lt a.rev b.rev) := hok.1.sublist hsub
    have heq : sint.Z (restoreLastRev ents) = (L.length : Int) - 1 := by
      unfold restoreLastRev
      cases h : ents.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 h) (List.ne_nil_of_mem hin)
      | some e =>
        simp only
        have he := hsub.subset (List.mem_of_getLast? h)
        have hle := logEnts_main_le L hb e he
        rcases pairwise_getLast hsorted hin h with rfl | hlt
        · exact hstar_main
        · unfold Rev.lt at hlt
          rcases hlt with hlt | ⟨heq, -⟩
          · omega
          · rw [← heq]; exact hstar_main
    omega
  · -- the last revision's entry was deleted: at or below the restored revision
    obtain ⟨-, rv, t, hrb, -, hrc, -⟩ := hdel estar hstar_mem hin
    have := revBytes_rev_inj hrb
    rw [← this] at hrc
    have hcm := CmpRecs.crev_le_max r
    omega

end pure

end mvcc
end EtcdGrove
end Perennial
