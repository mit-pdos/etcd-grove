/-
**M2, the storage side, step 2: the index `restore()` rebuilds from a compacted bucket (Draft,
pure)** (`notes/m2-storage-plan.md`, "After review round 4", A1 (b)). Imported by mvcc's restore
Draft (`M2StorageDraftRestore.lean`); no `axiom`, no `sorry`; nothing switched.

**What `restoreIntoIndex` builds from a compacted `Key` bucket** (`kvstore.go:430-480`,
`key_index.go:105-126`): a key whose oldest surviving entry is a put gets
`restore(Revision{Main: kv.CreateRevision}, rev, kv.Version)`, which agrees with the compacted
key index (the generation cut to start at `rev` keeps the original `created` and `ver`); a key
whose oldest surviving entry is a tombstone gets `restoreTombstone`, a generation
`{created: 0, ver: 1, revs: [rev]}` and an empty one, where the compacted key index keeps the
original `created` and `ver` of the generation it cut down to its tombstone.

**So today's index invariant cannot hold after a restore over a compacted bucket**
(`idxCRep_restore_counterexample`, proved): `IdxCRep cmax evs idx` (`Compact.lean`, the
`RWMutex` resource's `HL`, `idxLockInv`) asks every key's index to be *equal* to the log's key index
compacted at some level, and no level gives the restored one (log `[[], [], [put a], [del a]]`,
compaction at `3`: the bucket keeps only the tombstone). The `created`/`ver` of a generation whose
only revision is its tombstone are never read (`kiGet` never answers a tombstone; compaction and
`keep` read revisions), so the repair is a modelling choice, internal to mvcc: the invariant compares
key indexes up to them (`kiNorm`, `IdxCRepN`); `kiGet_kiNorm` (proved) is the fact that readers see
no difference. This is the "index over a thinned bucket" item of the approval list (internal).

**The bucket's shape must be the job's** (`bucketThinnedAt_counterexample`, proved): the round-3
Draft's `bucketThinnedAt L c m` (every missing entry deletable at `c`) admits a bucket missing a
deletable revision while keeping an older one of the same key, from which the rebuilt index answers
a read at `c` with the wrong version. The compaction job deletes the deletable keys in revision order
(`scheduleCompaction`'s batches from revision 0 up, `kvstore_compaction.go`), and a finished earlier
compaction's deletions are deletable at a later one (`KeyDel` is monotone in `c`), so every image a
member can send has, per key, a *prefix* of its revisions removed: `bucketCutAt` (drafted below), in
place of `bucketThinnedAt`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreModel
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CompactIdx
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreChunks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ## Key indexes up to the unread header of a tombstone-only generation -/

/-- **A generation's unread header cleared** (draft): a generation that is not the last and has one
revision (its tombstone: a generation that is not the last ends with one) gets `created := 0`,
`ver := 1`, the values `restoreTombstone` gives it. -/
def genNorm (last : Bool) (g : Gen) : Gen :=
  if last = false ∧ g.revs.length = 1 then { g with created := W64 0, ver := W64 1 } else g

/-- **A key index up to the unread headers** (draft): every generation but the last normalized. -/
def kiNorm (ki : KeyIndex) : KeyIndex :=
  { ki with gens := ki.gens.mapIdx fun i g => genNorm (decide (i + 1 = ki.gens.length)) g }

/-- **The index, compacted per key, up to the unread headers** (draft of `IdxCRep`'s repair:
`idxLockInv`'s `HL` at the switch). -/
def IdxCRepN (cmax : Int) (evs : List Ev) (idx : IndexM) : Prop :=
  idx.Pairwise idxLess ∧
    ∀ k, ∃ c : Int, -1 ≤ c ∧ c ≤ cmax ∧
      (idxGet idx k).map kiNorm = (kiCompactO c (kiOfKey evs k)).map kiNorm

/-- Today's invariant gives the repaired one. -/
theorem IdxCRepN_of {cmax : Int} {evs : List Ev} {idx : IndexM} (h : IdxCRep cmax evs idx) :
    IdxCRepN cmax evs idx :=
  ⟨h.1, fun k => by
    obtain ⟨c, h0, h1, h2⟩ := h.2 k
    exact ⟨c, h0, h1, by rw [h2]⟩⟩


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

/-- **The repaired invariant holds there** (`IdxCRepN`, at level `3`): up to the tombstone-only
generation's header the rebuilt key index is the log's compacted at `3`. -/
theorem cx_idxCRepN : ∀ k, (idxGet (idxRestore [cxTombEnt]) k).map kiNorm =
    (kiCompactO (if k = cxKey then 3 else -1) (kiOfKey (evsOf cxLog) k)).map kiNorm := by
  intro k
  by_cases hk : k = cxKey
  · subst hk; rfl
  · rw [cx_idxRestore, cx_kiOfKey_other k hk,
      idxGet_none_of_not_mem (by simp) (fun v hv => hk (by simp at hv; exact hv.1))]
    simp only [hk, ↓reduceIte]
    rfl

/-! ## Readers see no difference -/

theorem kiNorm_length (ki : KeyIndex) : (kiNorm ki).gens.length = ki.gens.length := by
  simp [kiNorm]

theorem kiNorm_getD (ki : KeyIndex) (i : Nat) :
    (kiNorm ki).gens.getD i Gen.empty =
      if i < ki.gens.length then genNorm (decide (i + 1 = ki.gens.length)) (ki.gens.getD i Gen.empty)
      else Gen.empty := by
  unfold kiNorm
  simp only [List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  by_cases hi : i < ki.gens.length
  · simp [hi]
  · simp [hi]

theorem genNorm_revs (l : Bool) (g : Gen) : (genNorm l g).revs = g.revs := by
  unfold genNorm; split <;> rfl

theorem kiNorm_revs (ki : KeyIndex) (i : Nat) :
    ((kiNorm ki).gens.getD i Gen.empty).revs = (ki.gens.getD i Gen.empty).revs := by
  rw [kiNorm_getD]
  split
  · exact genNorm_revs _ _
  · rename_i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi), Gen.empty]

/-- The generation scan reads only the revisions. -/
theorem kiFindGenAux_congrRevs (gens gens' : List Gen) (a : w64) (hl : gens.length = gens'.length)
    (hr : ∀ i, (gens.getD i Gen.empty).revs = (gens'.getD i Gen.empty).revs) :
    ∀ n, kiFindGenAux gens a n = kiFindGenAux gens' a n
  | 0 => rfl
  | n + 1 => by
    rw [kiFindGenAux_succ, kiFindGenAux_succ]
    simp only [hr n, hl, kiFindGenAux_congrRevs gens gens' a hl hr n]

theorem kiFindGen_kiNorm (ki : KeyIndex) (a : w64) : kiFindGen (kiNorm ki) a = kiFindGen ki a := by
  unfold kiFindGen
  rw [kiNorm_length]
  exact kiFindGenAux_congrRevs _ _ a (kiNorm_length ki) (kiNorm_revs ki) _

/-- **Readers see no difference** (`kiGet`, what every read of the index answers): the scan never
stops at a generation that is not the last and has one revision (its tombstone, at or below every
revision the scan could stop there for), the only ones `kiNorm` changes. -/
theorem kiGet_kiNorm (ki : KeyIndex) (a : w64) : kiGet (kiNorm ki) a = kiGet ki a := by
  unfold kiGet
  rw [kiFindGen_kiNorm]
  cases hf : kiFindGen ki a with
  | none => rfl
  | some gx =>
    obtain ⟨hlt, hne, hnot, hhead⟩ := kiFindGenAux_spec ki.gens.length gx hf
    simp only
    have hg : (kiNorm ki).gens.getD gx Gen.empty = ki.gens.getD gx Gen.empty := by
      rw [kiNorm_getD]; simp only [hlt, ↓reduceIte]
      unfold genNorm
      split
      · rename_i h
        exfalso
        apply hnot
        obtain ⟨hl, h1⟩ := h
        refine ⟨by intro he; simp at hl; omega, ?_⟩
        generalize ki.gens.getD gx Gen.empty = g at *
        match g, h1 with
        | ⟨_, _, [r]⟩, _ => simpa using hhead
      · rfl
    rw [hg]

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

/-- **Why `KeyOnceAt`**: the job's cut just after revision `2` (deletable at `3`, as `⟨3, 0⟩` is)
leaves `⟨3, 0⟩, ⟨3, 1⟩`, rebuilt as one generation `{created 2, ver 3, [⟨3,0⟩, ⟨3,1⟩]}`
(`restore` at `⟨3, 0⟩`'s create revision and version `2`, then a put), which no compaction level
`-1 … 3` gives, even up to the headers: the levels below `3` keep revision `2`, `3` cuts to
`⟨3, 1⟩`. -/
theorem cx3_not_compacted (c : Int) (h0 : -1 ≤ c) (h1 : c ≤ 3) :
    (kiCompactO c (kiOfKey (evsOf cx3Log) cxKey)).map kiNorm ≠
      some (kiNorm (kiPut (kiRestore (W64 2) ⟨W64 3, W64 0⟩ (W64 2)) ⟨W64 3, W64 1⟩)) := by
  intro h
  have h' := congrArg (Option.map fun ki : KeyIndex => ki.gens.map fun g => (g.created, g.ver, g.revs)) h
  revert h'
  obtain rfl | rfl | rfl | rfl | rfl : c = -1 ∨ c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  all_goals decide

/-! ## The drafted shape and what the rebuild gives over it -/

/-- **Each key changes at most once in revision `r`** (pure; draft): etcd's transactions never
touch a key twice (`checkIntervals` rejects overlapping puts, and a put overlapping a delete, in one
request), so every revision of the committed log has it. Needed only where a compaction's job may
cut between two changes of one key in one revision (a batch boundary of `scheduleCompaction` falls
on any bucket key): with a put and then a delete or a put of the same key in revision `r`, a cut
just after the first leaves a key index no compaction level gives. `NoDelPutAt L r` is its
del-then-put case. -/
def KeyOnceAt (L : Log) (r : Nat) : Prop :=
  ((L.getD r []).map Change.key).Nodup

/-- **The job's shape** (draft, in place of `bucketThinnedAt`; A1 (b)): the image's `Key` entries
`ents` are the log's (in order) but for, per key, a prefix of its entries, each deletable by the
compaction at `c` (`KeyDel`). A finished compaction at `c` (every deletable entry gone), a leader's
bucket mid-job (the job deletes from revision `0` up, in batches), and either after an earlier
finished compaction (`KeyDel` grows with `c`) all have it. -/
def entsCutAt (L : Log) (c : Int) (ents : List KvEnt) : Prop :=
  ents.Sublist (logEnts L 0 L.length) ∧
    (∀ e ∈ logEnts L 0 L.length, e ∉ ents → KeyDel L c (revBytes e.rev e.tomb)) ∧
    ∀ e₁ ∈ logEnts L 0 L.length, ∀ e₂ ∈ logEnts L 0 L.length,
      e₁.kv.key = e₂.kv.key → Rev.lt e₁.rev e₂.rev → e₂ ∉ ents → e₁ ∉ ents

/-- The whole bucket has the shape at any revision. -/
theorem entsCutAt_full (L : Log) (c : Int) : entsCutAt L c (logEnts L 0 L.length) :=
  ⟨List.Sublist.refl _, fun _ h h' => absurd h h', fun _ _ _ h₂ _ _ h => absurd h₂ h⟩

/-- **What `restoreIntoIndex` rebuilds from the job's shape** (the statement, drafted; **not yet
proved**: the pure fact `store.restore.specR`'s index post rests on, A1 (b)): over a well-formed
log whose revisions up to `c` change each key once, the rebuilt index is the log's compacted per key
at a level of its own, at most `c`, up to the unread headers (`IdxCRepN c`). The level of a key
whose first surviving entry `e` follows dropped ones is `e`'s main revision, or `c` if that is past
`c`; of a key with nothing dropped, `-1`. The proof's route: the index per key is the fold of
`idxRestoreEnt` over the key's surviving entries (`idxGet_btInsert`); the first is `restore`d with
the entry's create revision and version, which are the key's generation's (`KvMatch`, `rev_step`),
so it is the log's key index up to that entry compacted at its revision (up to the header when it is
a tombstone); compaction commutes with the later events, all above the level (`kiCompact_kiPut`,
`kiCompactO_step`), and so does `kiNorm`. -/
def idxRestore_cutStmt : Prop :=
  ∀ (L : Log) (c : Int) (ents : List KvEnt),
    LogWf' L → LogB L → -1 ≤ c → c < L.length → (∀ r : Nat, (r : Int) ≤ c → KeyOnceAt L r) →
    entsCutAt L c ents → IdxCRepN c (evsOf L) (idxRestore ents)

/-- The whole bucket rebuilds the log's index (today's `idxRestore_logEnts'`), in the repaired
form, at any level. -/
theorem idxRestore_full_N (L : Log) (c : Int) (hc : -1 ≤ c) (hb : LogB L) (hwf : LogWf' L) :
    IdxCRepN c (evsOf L) (idxRestore (logEnts L 0 L.length)) := by
  rw [idxRestore_logEnts' L hb.1 hb.2 hwf]
  exact IdxCRepN_of ((idxCRep_indexOf L hb).mono hc)

end mvcc
end EtcdGrove
end Perennial
