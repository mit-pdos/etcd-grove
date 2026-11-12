/-
**M2, the storage side, step 2: the evidence for the index over a compacted bucket** (`notes/
m2-storage-plan.md`, "After review round 4", A1 (b), and "The index at a full revision (branch
m2-index)"). Pure; no `axiom`, no `sorry`. What it argued for is now real: the index invariant at a
full revision (`IdxCRepN`, `InvIndexCut.lean`, `idxLockInv`'s `HL`) and the rebuild theorem
(`idxRestore_cut`, `InvIndexRestore.lean`). This module keeps the counterexamples that shaped them.

**What `restoreIntoIndex` builds from a compacted `Key` bucket** (`kvstore.go:430-480`,
`key_index.go:105-126`): a key whose oldest surviving entry is a put gets
`restore(Revision{Main: kv.CreateRevision}, rev, kv.Version)`, which agrees with the key index cut
to start at `rev` (the cut keeps the generation's `created` and `ver`); a key whose oldest surviving
entry is a tombstone gets `restoreTombstone`, a generation `{created: 0, ver: 1, revs: [rev]}` and
an empty one, where the cut keeps the original `created` and `ver` of the generation it cut down to
its tombstone.

- **Equality with a compaction cannot hold** (`idxCRep_restore_counterexample`): the old invariant
  `IdxCRep` asked every key's index to *equal* the log's compacted at some level; the restored
  tombstone-only generation's header differs. Repaired by comparing up to that header (`kiNorm`),
  which nothing reads (`kiGet_kiNorm`).
- **The bucket's shape must be the job's** (`bucketThinnedAt_counterexample`): any deletable subset
  missing admits a wrong index; the job's shape is a prefix of each key's entries (`entsCutAt`).
- **A level at a main revision is not enough** (`cx3_not_compacted`, and the reviewer's log of round 5,
  `cxr_not_compacted`): a job's batch can stop between two sub-revisions of one main revision, after
  which the rebuilt key index starts at the key's first surviving *sub*-revision, which no compaction
  at a main revision gives, even up to the headers. Round 4 excluded it with a premise (`KeyOnceAt`,
  each key changed once per revision), which is no etcd guarantee
  (`issues/etcd-txn-check-intervals-sibling.md`: sibling transactions put and delete one key in one
  revision). The user's decision B1 (round 5) made the level a full revision instead: both logs'
  rebuilt indexes are related at it (`cx3_idxCRepN`, `cxr_idxCRepN`), as `idxRestore_cut` proves in
  general, with no premise on how often a revision changes a key.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndexRestore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ## The counterexample: today's invariant after a restore over a compacted bucket -/

/-- The key of the counterexample. -/
abbrev cxKey : GoString := [W8 97]

/-- The counterexample's log: revisions `0`, `1` empty (`[[], []] ++ R`), a put of the key at `2`,
its delete at `3`. -/
abbrev cxLog : Log := [[], [], [.put cxKey [W8 120] (W64 0)], [.del cxKey]]

/-- The key's index over the whole log: one generation `{created 2, ver 2, [2, 3]}`, then an empty
one. -/
theorem cx_kiOfKey : kiOfKey (evsOf cxLog) cxKey =
    { modified := ⟨W64 3, W64 0⟩,
      gens := [{ ver := W64 2, created := W64 2, revs := [⟨W64 2, W64 0⟩, ⟨W64 3, W64 0⟩] },
        Gen.empty] } := by
  rfl

/-- The put's bucket entry (revision `2`, created at `2`, version `1`). -/
abbrev cxPutEnt : KvEnt :=
  ⟨⟨W64 2, W64 0⟩, false,
    { key := cxKey, createRev := W64 2, modRev := W64 2, version := W64 1, value := [W8 120],
      lease := W64 0 }⟩

/-- The tombstone's bucket entry (revision `3`). -/
abbrev cxTombEnt : KvEnt := ⟨⟨W64 3, W64 0⟩, true, zeroKv cxKey⟩

/-- The log's `Key` bucket, as entries: the put, then the tombstone. -/
theorem cx_logEnts : logEnts cxLog 0 cxLog.length = [cxPutEnt, cxTombEnt] := by
  rfl

/-- Another key has no event. -/
theorem cx_kiOfKey_other (k : GoString) (hk : k ≠ cxKey) : kiOfKey (evsOf cxLog) k = kiEmpty := by
  have he : evsOf cxLog = [{ rev := ⟨W64 2, W64 0⟩, change := .put cxKey [W8 120] (W64 0) },
      { rev := ⟨W64 3, W64 0⟩, change := .del cxKey }] := by rfl
  unfold kiOfKey
  rw [he]
  have hne : ¬ cxKey = k := fun h => hk h.symm
  simp [Ev.key, Change.key, hne]

/-- Compaction at `3` keeps the tombstone (`doCompact`'s `available`): the put is deletable. -/
theorem cx_keyDel : KeyDel cxLog 3 (revBytes cxPutEnt.rev cxPutEnt.tomb) := by
  refine ⟨by decide, cxPutEnt.rev, false, rfl, by decide, by decide, ?_⟩
  rintro ⟨k, hk⟩
  by_cases hkk : k = cxKey
  · subst hkk
    have : kiAvail (W64 3) (kiOfKey (evsOf cxLog) cxKey) = some ⟨W64 3, W64 0⟩ := by rfl
    rw [this] at hk
    cases hk
  · have hki := cx_kiOfKey_other k hkk
    rw [hki] at hk
    have : kiAvail (W64 3) kiEmpty = none := by rfl
    rw [this] at hk
    cases hk

/-- The index rebuilt from what compaction at `3` leaves of the key's entries (the tombstone's):
`restoreTombstone`'s key index, `{created 0, ver 1, [3]}` and an empty generation. -/
theorem cx_idxRestore :
    idxRestore [cxTombEnt] = [(cxKey, kiRestoreTombstone ⟨W64 3, W64 0⟩)] := by
  rfl

/-- **No compaction level gives the rebuilt key index**: at levels `-1 … 2` the compacted index
keeps the put, at `3` the generation's header (`created 2`), at `4` none is left. -/
theorem cx_not_compacted (c : Int) (h0 : -1 ≤ c) (h1 : c ≤ 4) :
    kiCompactO c (kiOfKey (evsOf cxLog) cxKey) ≠ some (kiRestoreTombstone ⟨W64 3, W64 0⟩) := by
  intro h
  have h' := congrArg (Option.map fun ki : KeyIndex => ki.gens.map fun g => (g.created, g.revs)) h
  revert h'
  obtain rfl | rfl | rfl | rfl | rfl | rfl : c = -1 ∨ c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
    omega
  all_goals decide

/-- **Today's index invariant fails after a restore over a compacted bucket** (A1 (b)): the log
`cxLog`'s `Key` bucket compacted at `3` (every entry but the tombstone deletable at `3`) rebuilds
an index that is no compaction of the log's at any level the lock's invariant allows (`cmax` below
the committed log's length, `cxLog ++ [[]]`). So `idx_publish`, which takes `IdxCRep`, cannot be
used by `restore()` over a compacted image: the invariant must change (`IdxCRepN`). -/
theorem idxCRep_restore_counterexample :
    cxTombEnt ∈ logEnts cxLog 0 cxLog.length ∧
    (∀ e ∈ logEnts cxLog 0 cxLog.length, e ≠ cxTombEnt → KeyDel cxLog 3 (revBytes e.rev e.tomb)) ∧
    ∀ cmax : Int, cmax ≤ 4 → ¬ IdxCRep cmax (evsOf cxLog) (idxRestore [cxTombEnt]) := by
  refine ⟨by rw [cx_logEnts]; simp, ?_, ?_⟩
  · intro e he hne
    rw [cx_logEnts] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact cx_keyDel
    · exact absurd rfl hne
  · rintro cmax hc ⟨-, hrep⟩
    obtain ⟨c, h0, h1, hg⟩ := hrep cxKey
    rw [cx_idxRestore] at hg
    have hget : idxGet [(cxKey, kiRestoreTombstone ⟨W64 3, W64 0⟩)] cxKey =
        some (kiRestoreTombstone ⟨W64 3, W64 0⟩) := by rfl
    rw [hget] at hg
    exact cx_not_compacted c h0 (by omega) hg.symm

/-- **The invariant at a full revision holds there** (`IdxCRepN`, at level `3`, the key cut at its
tombstone, `(0, 1)`): up to the tombstone-only generation's header the rebuilt key index is the
log's cut there. -/
theorem cx_idxCRepN : IdxCRepN 3 (evsOf cxLog) (idxRestore [cxTombEnt]) := by
  refine ⟨by rw [cx_idxRestore]; simp, fun k => ?_⟩
  by_cases hk : k = cxKey
  · subst hk
    refine ⟨3, by decide, Int.le_refl _, 0, 1, ?_, ?_⟩
    · rw [cx_kiOfKey]; right; decide
    · rw [cx_kiOfKey]; rfl
  · refine ⟨-1, Int.le_refl _, by decide, 0, 0, ?_, ?_⟩
    · rw [cx_kiOfKey_other k hk]; right; decide
    · rw [cx_idxRestore, cx_kiOfKey_other k hk,
        idxGet_none_of_not_mem (by simp) (fun v hv => hk (by simp at hv; exact hv.1))]
      rfl

/-! ## The bucket's shape: a prefix of each key's revisions, not any deletable subset -/

/-- The second counterexample's log: three puts of the key, at `2`, `3`, `4`. -/
abbrev cx2Log : Log :=
  [[], [], [.put cxKey [W8 120] (W64 0)], [.put cxKey [W8 121] (W64 0)],
    [.put cxKey [W8 122] (W64 0)]]

/-- A put's bucket entry of `cx2Log` (revision `r`, version `v`, value `x`). -/
abbrev cx2Ent (r v : w64) (x : GoString) : KvEnt :=
  ⟨⟨r, W64 0⟩, false,
    { key := cxKey, createRev := W64 2, modRev := r, version := v, value := x, lease := W64 0 }⟩

theorem cx2_logEnts : logEnts cx2Log 0 cx2Log.length =
    [cx2Ent (W64 2) (W64 1) [W8 120], cx2Ent (W64 3) (W64 2) [W8 121],
      cx2Ent (W64 4) (W64 3) [W8 122]] := by
  rfl

/-- Compaction at `4` keeps only revision `4`: `3` is deletable. -/
theorem cx2_keyDel3 : KeyDel cx2Log 4 (revBytes ⟨W64 3, W64 0⟩ false) := by
  refine ⟨by decide, ⟨W64 3, W64 0⟩, false, rfl, by decide, by decide, ?_⟩
  rintro ⟨k, hk⟩
  by_cases hkk : k = cxKey
  · subst hkk
    have : kiAvail (W64 4) (kiOfKey (evsOf cx2Log) cxKey) = some ⟨W64 4, W64 0⟩ := by rfl
    rw [this] at hk
    cases hk
  · have he : evsOf cx2Log = [{ rev := ⟨W64 2, W64 0⟩, change := .put cxKey [W8 120] (W64 0) },
        { rev := ⟨W64 3, W64 0⟩, change := .put cxKey [W8 121] (W64 0) },
        { rev := ⟨W64 4, W64 0⟩, change := .put cxKey [W8 122] (W64 0) }] := by rfl
    have hki : kiOfKey (evsOf cx2Log) k = kiEmpty := by
      unfold kiOfKey
      rw [he]
      have hne : ¬ cxKey = k := fun h => hkk h.symm
      simp [Ev.key, Change.key, hne]
    rw [hki] at hk
    have : kiAvail (W64 4) kiEmpty = none := by rfl
    rw [this] at hk
    cases hk

/-- **The round-3 shape admits a wrong index** (`bucketThinnedAt`, every missing entry deletable):
the `Key` bucket of `cx2Log` without revision `3` (deletable at `4`) but with revision `2` (also
deletable, kept) rebuilds a key index that answers a read at revision `4` (at the compaction
revision) with version `2` where the log's answers `3`. No member's image has this shape: the job
deletes in revision order. -/
theorem bucketThinnedAt_counterexample :
    (∀ e ∈ logEnts cx2Log 0 cx2Log.length,
        e ∉ [cx2Ent (W64 2) (W64 1) [W8 120], cx2Ent (W64 4) (W64 3) [W8 122]] →
        KeyDel cx2Log 4 (revBytes e.rev e.tomb)) ∧
    (kiGet ((idxGet (idxRestore [cx2Ent (W64 2) (W64 1) [W8 120], cx2Ent (W64 4) (W64 3) [W8 122]])
        cxKey).getD kiEmpty) (W64 4)).map (fun p => p.2.2) = some (W64 2) ∧
    (kiGet (kiOfKey (evsOf cx2Log) cxKey) (W64 4)).map (fun p => p.2.2) = some (W64 3) := by
  refine ⟨?_, by rfl, by rfl⟩
  intro e he hne
  rw [cx2_logEnts] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he hne
  rcases he with rfl | rfl | rfl
  · exact absurd (Or.inl rfl) hne
  · exact cx2_keyDel3
  · exact absurd (Or.inr rfl) hne

/-- The third counterexample's log: the key put at `2`, then twice in revision `3`. -/
abbrev cx3Log : Log :=
  [[], [], [.put cxKey [W8 120] (W64 0)], [.put cxKey [W8 121] (W64 0), .put cxKey [W8 122] (W64 0)]]

theorem cx3_kiOfKey : kiOfKey (evsOf cx3Log) cxKey =
    { modified := ⟨W64 3, W64 1⟩,
      gens := [{ ver := W64 3, created := W64 2, revs := [⟨W64 2, W64 0⟩, ⟨W64 3, W64 0⟩, ⟨W64 3, W64 1⟩] }] } := by
  rfl

theorem cx3_kiOfKey_other (k : GoString) (hk : k ≠ cxKey) : kiOfKey (evsOf cx3Log) k = kiEmpty := by
  have he : evsOf cx3Log = [{ rev := ⟨W64 2, W64 0⟩, change := .put cxKey [W8 120] (W64 0) },
      { rev := ⟨W64 3, W64 0⟩, change := .put cxKey [W8 121] (W64 0) },
      { rev := ⟨W64 3, W64 1⟩, change := .put cxKey [W8 122] (W64 0) }] := by rfl
  unfold kiOfKey
  rw [he]
  have hne : ¬ cxKey = k := fun h => hk h.symm
  simp [Ev.key, Change.key, hne]

/-- `cx3Log`'s `Key` bucket. -/
abbrev cx3Ents : List KvEnt := logEnts cx3Log 0 cx3Log.length

/-- **No compaction at a main revision gives it** (why round 4 needed `KeyOnceAt`): the job's cut
just after revision `2` (deletable at `3`, as `⟨3, 0⟩` is) leaves `⟨3, 0⟩, ⟨3, 1⟩`, rebuilt as one
generation `{created 2, ver 3, [⟨3,0⟩, ⟨3,1⟩]}` (`restore` at `⟨3, 0⟩`'s create revision and version
`2`, then a put), which no compaction level `-1 … 3` gives, even up to the headers: the levels below
`3` keep revision `2`, `3` cuts to `⟨3, 1⟩`. -/
theorem cx3_not_compacted (c : Int) (h0 : -1 ≤ c) (h1 : c ≤ 3) :
    (kiCompactO c (kiOfKey (evsOf cx3Log) cxKey)).map kiNorm ≠
      some (kiNorm (kiPut (kiRestore (W64 2) ⟨W64 3, W64 0⟩ (W64 2)) ⟨W64 3, W64 1⟩)) := by
  intro h
  have h' := congrArg (Option.map fun ki : KeyIndex => ki.gens.map fun g => (g.created, g.ver, g.revs)) h
  revert h'
  obtain rfl | rfl | rfl | rfl | rfl : c = -1 ∨ c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  all_goals decide

/-- The rebuilt index over `cx3Log`'s bucket with revision `2` deleted (the batch boundary after
it): `restore` of `⟨3, 0⟩` (created `2`, version `2`), then a put of `⟨3, 1⟩`. -/
theorem cx3_idxRestore : idxRestore (cx3Ents.drop 1) =
    [(cxKey, kiPut (kiRestore (W64 2) ⟨W64 3, W64 0⟩ (W64 2)) ⟨W64 3, W64 1⟩)] := by
  rfl

/-- **At a full revision, the third counterexample is gone** (`IdxCRepN 3`, the key cut at
`⟨3, 0⟩`, position `(0, 1)`). -/
theorem cx3_idxCRepN : IdxCRepN 3 (evsOf cx3Log) (idxRestore (cx3Ents.drop 1)) := by
  rw [cx3_idxRestore]
  refine ⟨by simp, fun k => ?_⟩
  by_cases hk : k = cxKey
  · subst hk
    refine ⟨3, by decide, Int.le_refl _, 0, 1, ?_, ?_⟩
    · rw [cx3_kiOfKey]; right; decide
    · rw [cx3_kiOfKey]; rfl
  · refine ⟨-1, Int.le_refl _, by decide, 0, 0, ?_, ?_⟩
    · rw [cx3_kiOfKey_other k hk]; right; decide
    · rw [cx3_kiOfKey_other k hk,
        idxGet_none_of_not_mem (by simp) (fun v hv => hk (by simp at hv; exact hv.1))]
      rfl

/-! ## The reviewer's log (review round 5, B1): a put and a delete of one key in one revision -/

/-- The log of round 5's B1: `a` put at `2`; then put at `⟨3, 0⟩` and deleted at `⟨3, 1⟩` (sibling
transactions of one request, which `checkIntervals` admits). -/
abbrev cxrLog : Log :=
  [[], [], [.put cxKey [W8 120] (W64 0)], [.put cxKey [W8 121] (W64 0), .del cxKey]]

theorem cxr_kiOfKey : kiOfKey (evsOf cxrLog) cxKey =
    { modified := ⟨W64 3, W64 1⟩,
      gens := [{ ver := W64 3, created := W64 2, revs := [⟨W64 2, W64 0⟩, ⟨W64 3, W64 0⟩, ⟨W64 3, W64 1⟩] },
        Gen.empty] } := by
  rfl

theorem cxr_kiOfKey_other (k : GoString) (hk : k ≠ cxKey) : kiOfKey (evsOf cxrLog) k = kiEmpty := by
  have he : evsOf cxrLog = [{ rev := ⟨W64 2, W64 0⟩, change := .put cxKey [W8 120] (W64 0) },
      { rev := ⟨W64 3, W64 0⟩, change := .put cxKey [W8 121] (W64 0) },
      { rev := ⟨W64 3, W64 1⟩, change := .del cxKey }] := by rfl
  unfold kiOfKey
  rw [he]
  have hne : ¬ cxKey = k := fun h => hk h.symm
  simp [Ev.key, Change.key, hne]

/-- The log's `Key` bucket: the put at `2`, the put at `⟨3, 0⟩` (created at `2`, version `2`), the
tombstone at `⟨3, 1⟩`. -/
theorem cxr_logEnts : logEnts cxrLog 0 cxrLog.length =
    [⟨⟨W64 2, W64 0⟩, false,
       { key := cxKey, createRev := W64 2, modRev := W64 2, version := W64 1, value := [W8 120], lease := W64 0 }⟩,
     ⟨⟨W64 3, W64 0⟩, false,
       { key := cxKey, createRev := W64 2, modRev := W64 3, version := W64 2, value := [W8 121], lease := W64 0 }⟩,
     ⟨⟨W64 3, W64 1⟩, true, zeroKv cxKey⟩] := by
  rfl

/-- **No compaction at a main revision gives the rebuilt key index** (the reviewer's hand-worked
case, now checked): after the job's batch stops just after revision `2`, the bucket keeps
`⟨3, 0⟩, ⟨3, 1⟩`, rebuilt as `{created 2, ver 3, [⟨3,0⟩, ⟨3,1⟩]}` and an empty generation; the
levels `-1 … 2` keep revision `2`, level `3` cuts to `⟨3, 1⟩`. -/
theorem cxr_not_compacted (c : Int) (h0 : -1 ≤ c) (h1 : c ≤ 3) :
    (kiCompactO c (kiOfKey (evsOf cxrLog) cxKey)).map kiNorm ≠
      (idxGet (idxRestore ((logEnts cxrLog 0 cxrLog.length).drop 1)) cxKey).map kiNorm := by
  intro h
  have h' := congrArg (Option.map fun ki : KeyIndex => ki.gens.map fun g => (g.created, g.ver, g.revs)) h
  revert h'
  obtain rfl | rfl | rfl | rfl | rfl : c = -1 ∨ c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  all_goals decide

/-- **At a full revision, the reviewer's case is related** (`IdxCRepN 3`, the key cut at `⟨3, 0⟩`,
position `(0, 1)`): the rebuilt key index is the log's with revision `2` dropped. -/
theorem cxr_idxCRepN : IdxCRepN 3 (evsOf cxrLog) (idxRestore ((logEnts cxrLog 0 cxrLog.length).drop 1)) := by
  have hr : idxRestore ((logEnts cxrLog 0 cxrLog.length).drop 1) =
      [(cxKey, kiTombstone (kiRestore (W64 2) ⟨W64 3, W64 0⟩ (W64 2)) ⟨W64 3, W64 1⟩)] := by
    rw [cxr_logEnts]; rfl
  rw [hr]
  refine ⟨by simp, fun k => ?_⟩
  by_cases hk : k = cxKey
  · subst hk
    refine ⟨3, by decide, Int.le_refl _, 0, 1, ?_, ?_⟩
    · rw [cxr_kiOfKey]; right; decide
    · rw [cxr_kiOfKey]; rfl
  · refine ⟨-1, Int.le_refl _, by decide, 0, 0, ?_, ?_⟩
    · rw [cxr_kiOfKey_other k hk]; right; decide
    · rw [cxr_kiOfKey_other k hk,
        idxGet_none_of_not_mem (by simp) (fun v hv => hk (by simp at hv; exact hv.1))]
      rfl

/-- The whole bucket rebuilds the log's index (today's `idxRestore_logEnts'`), at any level. -/
theorem idxRestore_full_N (L : Log) (c : Int) (hc : -1 ≤ c) (hb : LogB L) (hwf : LogWf' L) :
    IdxCRepN c (evsOf L) (idxRestore (logEnts L 0 L.length)) := by
  rw [idxRestore_logEnts' L hb.1 hb.2 hwf]
  exact IdxCRepN_of ((idxCRep_indexOf L hb).mono hc)

end mvcc
end EtcdGrove
end Perennial
