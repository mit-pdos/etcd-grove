/-
**A scan from the compaction revision reads every revision at or above it** (watches across a
compaction, W1, 2026-11-01; `notes/watch-compaction-plan.md`, D3). `rangeEvents` reads the key
bucket from `minRev`; on a compacting store the backend's snapshot is thin (`snapThin`: the bucket
less some keys compaction may delete, `delKey`). From `minRev` at or above the compaction revision
`c`, with revision `c` changing each key once (or no compaction), no bucket key it reads is one
compaction may delete, so the snapshot has every entry of the scanned range.

* `ev_mem_kiRevs`: every event of a well-formed log is a revision of its key's index (a put always
  is; a delete is of a present key, `kiLastEmpty_false_of_del`).
* `bucket_entry_ev`: a bucket entry is the bytes of an event's revision.
* `snapThin_scan`: with a share of the compaction revision's authority at `c`, a thin snapshot of
  a certified log's bucket has every entry at a revision at or above `c`, when revision `c` changes
  each key once (or `c = -1`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CompactNoDup
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Hist
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.SyncModel
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RevOrder

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-- A prefix of the last revision's changes keeps the log well formed. -/
theorem LogWf'.take_last {ilog : Log} {pend rest : List Change}
    (h : LogWf' (ilog ++ [pend ++ rest])) : LogWf' (ilog ++ [pend]) := by
  refine ⟨fun _ => ?_, fun r cs i k hr hi => ?_⟩
  · have := h.1 (by simp)
    rcases Nat.eq_zero_or_pos ilog.length with h0 | hpos
    · rw [List.length_eq_zero_iff] at h0; subst h0
      simp at this ⊢
      exact this.1
    · rw [List.getElem?_append_left hpos] at this ⊢; exact this
  · by_cases hlt : r < ilog.length
    · rw [List.getElem?_append_left hlt] at hr
      have := h.2 r cs i k (by rw [List.getElem?_append_left hlt]; exact hr) hi
      rw [stateAt_append_lt _ _ (by omega)] at this ⊢
      exact this
    · have hr' : r = ilog.length := by
        have := (List.getElem?_eq_some_iff.1 hr).1; simp at this; omega
      subst hr'
      rw [List.getElem?_append_right (Nat.le_refl _)] at hr
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hr
      subst hr
      have hi' : (pend ++ rest)[i]? = some (.del k) := by
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hi).1]; exact hi
      have := h.2 ilog.length (pend ++ rest) i k
        (by rw [List.getElem?_append_right (Nat.le_refl _)]; simp) hi'
      have htake : (pend ++ rest).take i = pend.take i := by
        rw [List.take_append_of_le_length (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hi).1)]
      rw [htake] at this
      rcases Nat.eq_zero_or_pos ilog.length with h0 | hpos
      · -- revision `0` is empty: no delete in it
        rw [List.length_eq_zero_iff] at h0; subst h0
        have h1 := h.1 (by simp)
        simp at h1
        rw [h1.1] at hi; simp at hi
      rw [stateAt_append_lt _ _ (by omega)] at this ⊢
      exact this

/-- **Every event of a well-formed log is a revision of its key's index.** -/
theorem ev_mem_kiRevs : ∀ (log : Log), LogWf' log → log.length < 2 ^ 63 →
    (∀ cs ∈ log, cs.length < 2 ^ 63) →
    ∀ e ∈ evsOf log, e.rev ∈ kiRevs (kiOfKey (evsOf log) e.key) := by
  refine snoc_induction (P := fun log => LogWf' log → log.length < 2 ^ 63 →
    (∀ cs ∈ log, cs.length < 2 ^ 63) →
    ∀ e ∈ evsOf log, e.rev ∈ kiRevs (kiOfKey (evsOf log) e.key)) ?_ ?_
  · intro _ _ _ e he; simp [evsOf] at he
  intro ilog cs ih hwf hlen hcs
  have hwf0 : LogWf' ilog := hwf.prefix
  have hlen0 : ilog.length < 2 ^ 63 := by simp at hlen; omega
  have hlen1 : ilog.length + 1 < 2 ^ 63 := by simp at hlen; omega
  have hcs0 : ∀ c ∈ ilog, c.length < 2 ^ 63 := fun c hc => hcs c (List.mem_append_left _ hc)
  have ih' := ih hwf0 hlen0 hcs0
  -- the changes of the last revision, one by one
  have key : ∀ (pend rest : List Change), pend ++ rest = cs →
      ∀ e ∈ evsOf (ilog ++ [pend]), e.rev ∈ kiRevs (kiOfKey (evsOf (ilog ++ [pend])) e.key) := by
    intro pend
    refine snoc_induction (P := fun pend => ∀ rest, pend ++ rest = cs →
      ∀ e ∈ evsOf (ilog ++ [pend]), e.rev ∈ kiRevs (kiOfKey (evsOf (ilog ++ [pend])) e.key)) ?_ ?_ pend
    · intro rest _ e he
      rw [evsOf_append] at he ⊢
      simp only [evsOfRev, List.zipIdx_nil, List.map_nil, List.append_nil] at he ⊢
      exact ih' e he
    · intro pend c ihp rest hcs' e he
      have hwfp : LogWf' (ilog ++ [pend ++ [c]]) := by
        rw [← hcs'] at hwf; exact LogWf'.take_last (rest := rest) hwf
      have ihp' := ihp ([c] ++ rest) (by rw [← List.append_assoc]; exact hcs')
      have hstr := fun k => (kiOfKey_struct k (evsOf (ilog ++ [pend]))).1
      rw [evsOf_append_change] at he ⊢
      have hgrow : ∀ (k : GoString) (r : Rev),
          r ∈ kiRevs (kiOfKey (evsOf (ilog ++ [pend])) k) →
          r ∈ kiRevs (kiOfKey (evsOf (ilog ++ [pend]) ++ [evOfChange ilog.length pend.length c]) k) := by
        intro k r hr
        rw [kiOfKey_append]
        split
        · rcases kiRevs_kiApply (hstr k) (evOfChange ilog.length pend.length c) with h | h <;>
            rw [h]
          · exact hr
          · exact List.mem_append_left _ hr
        · exact hr
      rcases List.mem_append.1 he with hold | hnew
      · exact hgrow _ _ (ihp' e hold)
      · rw [List.mem_singleton] at hnew
        subst hnew
        rw [kiOfKey_append, if_pos rfl]
        unfold kiApply
        split
        · rename_i htomb
          -- a delete: of a present key, so its index's last generation is not empty
          obtain ⟨k, hk⟩ : ∃ k, c = .del k := by
            cases c with
            | put _ _ _ => simp [evOfChange, Ev.tomb, Change.isDel] at htomb
            | del k => exact ⟨k, rfl⟩
          subst hk
          have hilog : 1 ≤ ilog.length := by
            rcases Nat.eq_zero_or_pos ilog.length with h0 | hpos
            · rw [List.length_eq_zero_iff] at h0; subst h0
              have := hwfp.1 (by simp)
              simp at this
            · exact hpos
          have hpl : pend.length < 2 ^ 63 := by
            have := hcs cs (List.mem_append_right _ (List.mem_singleton_self _))
            rw [← hcs'] at this; simp at this; omega
          have hle := kiLastEmpty_false_of_del ilog pend k
            (by have := hwfp; rw [show pend ++ [Change.del k] = pend ++ [Change.del k] from rfl] at this
                exact LogWf'.take_last (rest := [Change.del k]) this)
            hwfp hlen1 hilog hpl hcs0
          have hke : (evOfChange ilog.length pend.length (Change.del k)).key = k := rfl
          rw [hke, hle]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [kiRevs_kiTombstone (hstr k).ne]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        · rw [kiRevs_kiPut (hstr _).ne]
          exact List.mem_append_right _ (List.mem_singleton_self _)
  intro e he
  exact key cs [] (List.append_nil _) e he

/-- The event of a change of the log is in its events. -/
theorem mem_evsOf_of (log : Log) (n i : Nat) (cs : List Change) (ch : Change)
    (hn : log[n]? = some cs) (hi : cs[i]? = some ch) :
    ({ rev := ⟨W64 n, W64 i⟩, change := ch } : Ev) ∈ evsOf log := by
  unfold evsOf
  rw [List.mem_flatten]
  refine ⟨evsOfRev n cs, List.mem_map.2 ⟨(cs, n), List.mem_zipIdx_iff_getElem?.2 hn, rfl⟩, ?_⟩
  unfold evsOfRev
  exact List.mem_map.2 ⟨(ch, i), List.mem_zipIdx_iff_getElem?.2 hi, rfl⟩

/-- **A bucket entry is the bytes of an event's revision.** -/
theorem bucket_entry_ev (log : Log) (hlen : log.length < 2 ^ 63)
    (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) (k v : GoString) (h : bucketMap log !! k = some v) :
    ∃ (n i : Nat) (ch : Change) (t : Bool), n < log.length ∧ k = revBytes ⟨W64 n, W64 i⟩ t ∧
      ({ rev := ⟨W64 n, W64 i⟩, change := ch } : Ev) ∈ evsOf log ∧
      ∃ cs, log[n]? = some cs ∧ cs[i]? = some ch := by
  have hm := (bucketMap_lookup_iff log hlen hcs k v).1 h
  unfold bucketOf at hm
  rw [List.mem_flatten] at hm
  obtain ⟨l, hl, hkv⟩ := hm
  rw [List.mem_map] at hl
  obtain ⟨⟨cs, n⟩, hp, rfl⟩ := hl
  have hn : log[n]? = some cs := List.mem_zipIdx_iff_getElem?.1 hp
  obtain ⟨i, t, hi, hk⟩ := RevOrder.mem_bucketOfRev hkv
  obtain ⟨ch, hch⟩ : ∃ ch, cs[i]? = some ch := ⟨cs[i], List.getElem?_eq_getElem hi⟩
  exact ⟨n, i, ch, t, (List.getElem?_eq_some_iff.1 hn).1, hk, mem_evsOf_of log n i cs ch hn hch,
    cs, hn, hch⟩

/-- **Two buckets that agree from `klo` on give the same scan from it**: every entry of `m'` is
`m`'s, and every entry of `m` at or above `klo` is `m'`'s. -/
theorem bucketRange_eq_of_agree (m m' : GMap GoString GoString) (klo khi : GoString)
    (hsub : ∀ k v, m' !! k = some v → m !! k = some v)
    (hge : ∀ k v, m !! k = some v → go.GoStringLe klo k → m' !! k = some v) :
    bucketRange m' klo khi = bucketRange m klo khi := by
  obtain ⟨hs, hmem⟩ := (bucketRange_eq_iff m klo khi (bucketRange m klo khi)).1 rfl
  apply (bucketRange_eq_iff m' klo khi _).2
  refine ⟨hs, fun k v => ?_⟩
  rw [hmem]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨hge k v h1 h2, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨hsub k v h1, h2, h3⟩

section scan
open Iris Iris.BI Iris.ProofMode
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A thin snapshot has every entry from the compaction revision on** (see the file header):
with a share of the compaction revision's authority at `c`, a thin snapshot `m'` of the bucket of
a certified log has every entry of the bucket at a revision at or above `lo ≥ c`, when revision
`c` changes each key once or there is no compaction (`c = -1`). -/
theorem snapThin_scan (γ : StoreNames) (q : Qp) (c : Int) (log : Log) (m' : Bucket) (lo : Nat)
    (hwf : LogWf' log) (hlen : log.length < 2 ^ 63) (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63)
    (hc : -1 ≤ c) (hclo : c ≤ lo) (hlo : lo < 2 ^ 63) (hnd : c = -1 ∨ oneChangePerKeyAt log c) :
    crevUB (GF := GF) γ.idx q c ∗ snapThin (bucketMap log) m' (delKey γ) ∗ idxCert γ.idx log ⊢
      crevUB γ.idx q c ∗ ⌜∀ k v, bucketMap log !! k = some v →
        go.GoStringLe (revBytes ⟨W64 (lo : Int), W64 0⟩ false) k → m' !! k = some v⌝ := by
  iintro ⟨Hu, Ht, #Hcert⟩
  iunfold snapThin at Ht
  icases Ht with ⟨%Hsub, #Hdel⟩
  by_cases hall : ∀ k v, bucketMap log !! k = some v →
      go.GoStringLe (revBytes ⟨W64 (lo : Int), W64 0⟩ false) k → m' !! k = some v
  · iframe Hu; ipureintro; exact hall
  iexfalso
  have hex : ∃ k v, bucketMap log !! k = some v ∧
      go.GoStringLe (revBytes ⟨W64 (lo : Int), W64 0⟩ false) k ∧ m' !! k ≠ some v :=
    Classical.byContradiction fun hn => hall fun k v h1 h2 =>
      Classical.byContradiction fun h3 => hn ⟨k, v, h1, h2, h3⟩
  obtain ⟨k, v, hk, hge, hne⟩ := hex
  -- the snapshot lacks `k` (an entry it has is the bucket's)
  have hnone : m' !! k = none := by
    cases h : m' !! k with
    | none => rfl
    | some v' =>
      have := Hsub k v' h
      rw [hk] at this
      cases this
      exact absurd h hne
  -- so compaction may delete it: a revision at most a certified compaction revision `c' ≤ c`
  have hkn : (bucketMap log).lookup k = some v ∧ m'.lookup k = none := ⟨hk, hnone⟩
  ihave #Hd := Hdel $$ %k %v %hkn
  iunfold delKey at Hd
  icases Hd with ⟨%c', %log', #Hlb, #Hcert', %Hkd⟩
  obtain ⟨hc', hkd⟩ := Hkd
  ihave %Hcc := crevUB_lb γ.idx q c c' hc hc' $$ Hu Hlb
  ihave %Hpre := idxCert_prefix γ.idx log log' $$ [$Hcert $Hcert']
  iunfold idxCert at Hcert'
  icases Hcert' with ⟨-, %Hwf', -, -⟩
  obtain ⟨-, hlen', hcs'⟩ := Hwf'
  ipureintro
  obtain ⟨n, i, ch, t, hn, hkeq, hev, cs, hcsn, hch⟩ := bucket_entry_ev log hlen hcs k v hk
  obtain ⟨hc'len, r, t', hk', h0, h1, hkeep⟩ := hkd
  have hr : r = ⟨W64 (n : Int), W64 (i : Int)⟩ := (revBytes_rev_inj (hkeq.symm.trans hk')).symm
  have hil : i < 2 ^ 63 := by
    have := hcs cs (List.mem_of_getElem? hcsn)
    have := (List.getElem?_eq_some_iff.1 hch).1
    omega
  have hnz : sint.Z (W64 (n : Int)) = n := by
    have : (n : Int) < 2 ^ 63 := by omega
    word
  have hlon : lo ≤ n := by
    rw [hkeq] at hge
    exact (revKey_ge lo n i t (by omega) (by omega) (by omega)).1 hge
  rw [hr, hnz] at h1
  -- the revision is at `c' = c`, the compaction revision itself
  have hnc : (n : Int) = c ∧ c' = c := by omega
  rcases hnd with hneg | hnd
  · omega
  have hkdl : KeyDel log c' k := by
    rcases Hpre with hp | hp
    · exact (KeyDel_prefix log log' hp ⟨hlen', hcs'⟩ c' hc' (by omega) k).1
        ⟨hc'len, r, t', hk', h0, by rw [hr, hnz]; exact h1, hkeep⟩
    · exact (KeyDel_prefix log' log hp ⟨hlen, hcs⟩ c' hc' hc'len k).2
        ⟨hc'len, r, t', hk', h0, by rw [hr, hnz]; exact h1, hkeep⟩
  have hmem := ev_mem_kiRevs log hwf hlen hcs _ hev
  rw [hk'] at hkdl
  rw [hnc.2] at hkdl
  exact not_KeyDel_of_noDup log ⟨hlen, hcs⟩ c (by omega) hnd ch.key r (by rw [hr]; exact hmem)
    (by rw [hr, hnz]; exact hnc.1) t' hkdl

end scan

end mvcc
end EtcdGrove
end Perennial
