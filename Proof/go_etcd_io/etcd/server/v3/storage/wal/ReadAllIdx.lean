/- Lean-first (no Rocq counterpart).

# `ReadAll`'s handle, the index bounds (W3/W5 of `notes/wal-fsext-plan.md`, twenty-seventh session)

What `walOpenWF`'s `walHandleIn` needs of `w.enti`/`w.snapi` after the loop (obligation (d)), pure, over
the records' `(type, data)` (`raIdxT`, `raIdx`'s step on them):

* `raIdxT_snap_le`: `w.snapi` is at least every snapshot record's index read; `entG_le`: `w.enti` at
  least the last entry record's index (`entG`, the entries' fold of `walLastIdx`);
* `segsDs_entG`, `snap_mem_segsDs`: on the records of segments, those folds are the operations';
* `readAll_idxD`: the history's `walLastIdx` and `walMaxSnapIdx` below the indices, given the
  operations before the read below `w.snapi`; with no index `2^64 - 1` in the history
  (`walHasMaxIdx`, the invariant's `WalsBounded`), `max(enti, snapi) + 1 < 2^64`;
* `raStep_matched`: a matched start has its snapshot record among those read.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllWFPure

@[expose] public section

set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

section pure
variable [GooseExts]

/-- `raIdx`'s step on a record's `(type, data)`. -/
def raIdxT (U : WalUnmarshal) (s : w64 × w64) (ix : w64 × w64) (td : w64 × List w8) : w64 × w64 :=
  raIdx U s ix ⟨td.1, 0#32, td.2⟩

theorem foldl_raIdx_map (U : WalUnmarshal) (s : w64 × w64) :
    ∀ (L : List WalRec) (ix : w64 × w64),
      L.foldl (raIdx U s) ix = (L.map (fun r => (r.typ, r.data))).foldl (raIdxT U s) ix
  | [], _ => rfl
  | r :: L, ix => by
    simp only [List.foldl_cons, List.map_cons]
    exact foldl_raIdx_map U s L _

/-- The entries' fold of `walLastIdx` on records: an entry record sets it to its index. -/
def entG (U : WalUnmarshal) (v : Nat) (td : w64 × List w8) : Nat :=
  if td.1 = entryType then
    match U.decEntry td.2 with
    | some e => uint.nat e.Index'
    | none => v
  else v

theorem raIdxT_snd_mono (U : WalUnmarshal) (s : w64 × w64) (ix : w64 × w64) (td : w64 × List w8) :
    uint.nat ix.2 ≤ uint.nat (raIdxT U s ix td).2 := by
  unfold raIdxT raIdx
  simp only
  split
  · split <;> simp
  · split
    · split
      · simp only
        split <;> omega
      · simp
    · simp

/-- **`w.snapi` is at least every snapshot record's index read** (and its start). -/
theorem raIdxT_snap_le (U : WalUnmarshal) (s : w64 × w64) :
    ∀ (L : List (w64 × List w8)) (ix : w64 × w64),
      uint.nat ix.2 ≤ uint.nat (L.foldl (raIdxT U s) ix).2 ∧
      ∀ td ∈ L, td.1 = snapshotType → ∀ p, U.decSnap td.2 = some p →
        uint.nat p.1 ≤ uint.nat (L.foldl (raIdxT U s) ix).2
  | [], ix => ⟨Nat.le_refl _, fun _ h => by cases h⟩
  | td :: L, ix => by
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := raIdxT_snap_le U s L (raIdxT U s ix td)
    refine ⟨Nat.le_trans (raIdxT_snd_mono U s ix td) h1, fun td' htd' ht p hp => ?_⟩
    rcases List.mem_cons.1 htd' with rfl | htd'
    · refine Nat.le_trans ?_ h1
      have hne : td'.1 ≠ entryType := by rw [ht]; decide
      unfold raIdxT raIdx
      simp only [if_neg hne, if_pos ht, hp]
      split <;> omega
    · exact h2 td' htd' ht p hp

/-- **`w.enti` is at least the last entry record's index read**. -/
theorem entG_le (U : WalUnmarshal) (s : w64 × w64) :
    ∀ (L : List (w64 × List w8)) (ix : w64 × w64) (v : Nat), v ≤ uint.nat ix.1 →
      L.foldl (entG U) v ≤ uint.nat (L.foldl (raIdxT U s) ix).1
  | [], _, _, h => h
  | td :: L, ix, v, h => by
    simp only [List.foldl_cons]
    apply entG_le U s L
    unfold entG raIdxT raIdx
    simp only
    by_cases he : td.1 = entryType
    · rw [if_pos he, if_pos he]
      cases U.decEntry td.2 <;> simp [h]
    · rw [if_neg he, if_neg he]
      split
      · split
        · simp only; split <;> omega
        · exact h
      · exact h

/-- The entries' fold from any start is at most the start or the fold from another. -/
theorem entG_start (U : WalUnmarshal) :
    ∀ (L : List (w64 × List w8)) (v w : Nat), L.foldl (entG U) v ≤ max v (L.foldl (entG U) w)
  | [], v, w => Nat.le_max_left _ _
  | td :: L, v, w => by
    simp only [List.foldl_cons]
    by_cases he : td.1 = entryType
    · unfold entG
      rw [if_pos he, if_pos he]
      cases U.decEntry td.2 with
      | none => exact entG_start U L v w
      | some e => exact Nat.le_max_right _ _
    · unfold entG
      rw [if_neg he, if_neg he]
      exact entG_start U L v w

/-- The entries' fold of `walLastIdx` on operations. -/
def lastEntF (x : Nat) (o : WalOp) : Nat :=
  match o with
  | .save _ es => (es.getLast?.map (fun e => uint.nat e.Index')).getD x
  | .snap _ _ => x

theorem walLastIdx_eq (P : WalHist) :
    walLastIdx P = max (P.foldl lastEntF 0) (walMaxSnapIdx P) := rfl

theorem entG_entries {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M) :
    ∀ (es : List EntryM) (v : Nat),
      (es.map (fun e => (entryType, M.encEntry e))).foldl (entG U) v =
        (es.getLast?.map (fun e => uint.nat e.Index')).getD v
  | [], v => rfl
  | e :: es, v => by
    simp only [List.map_cons, List.foldl_cons]
    have h1 : entG U v (entryType, M.encEntry e) = uint.nat e.Index' := by
      unfold entG; simp [hU.entry e]
    rw [h1, entG_entries hU es, List.getLast?_cons]
    cases es.getLast? <;> rfl

theorem entG_nonEntry (U : WalUnmarshal) :
    ∀ (L : List (w64 × List w8)) (v : Nat), (∀ td ∈ L, td.1 ≠ entryType) → L.foldl (entG U) v = v
  | [], _, _ => rfl
  | td :: L, v, h => by
    simp only [List.foldl_cons]
    have h1 : entG U v td = v := by unfold entG; rw [if_neg (h td (List.mem_cons_self ..))]
    rw [h1]
    exact entG_nonEntry U L v (fun td' h' => h td' (List.mem_cons_of_mem _ h'))

theorem entG_opDs {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M) (o : WalOp) (v : Nat) :
    (opDs M o).foldl (entG U) v = lastEntF v o := by
  cases o with
  | save h es =>
    simp only [opDs, List.foldl_append, lastEntF]
    rw [entG_entries hU es]
    apply entG_nonEntry
    intro td htd
    split at htd
    · cases htd
    · simp only [List.mem_singleton] at htd; subst htd; exact (by simp [entryType, stateType, snapshotType, metadataType, crcType])
  | snap m al =>
    simp only [opDs, List.foldl_cons, List.foldl_nil, lastEntF]
    unfold entG; rw [if_neg (by simp [entryType, stateType, snapshotType, metadataType, crcType])]

theorem entG_hdr (M : WalMarshal) (U : WalUnmarshal) (md : List w8) (first : Bool) (P : WalHist)
    (v : Nat) : (segHdrDs M md first P).foldl (entG U) v = v := by
  apply entG_nonEntry
  intro td htd
  unfold segHdrDs at htd
  split at htd
  · simp only [hdrDs, List.mem_cons, List.not_mem_nil, or_false] at htd
    rcases htd with rfl | rfl | rfl <;> exact (by simp [entryType, stateType, snapshotType, metadataType, crcType])
  · simp only [cutHdrDs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at htd
    rcases htd with (rfl | rfl) | htd
    · exact (by simp [entryType, stateType, snapshotType, metadataType, crcType])
    · exact (by simp [entryType, stateType, snapshotType, metadataType, crcType])
    · split at htd
      · cases htd
      · simp only [List.mem_singleton] at htd; subst htd; exact (by simp [entryType, stateType, snapshotType, metadataType, crcType])

/-- **On the records of segments, the entries' fold is the operations'**. -/
theorem segsDs_entG {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M) (md : List w8) :
    ∀ (first : Bool) (P : WalHist) (Ss : List WalHist) (v : Nat),
      (segsDs M md first P Ss).flatten.foldl (entG U) v = Ss.flatten.foldl lastEntF v
  | _, _, [], v => rfl
  | first, P, S :: Ss, v => by
    simp only [segsDs, List.flatten_cons, List.foldl_append, entG_hdr]
    rw [segsDs_entG hU md false (P ++ S) Ss]
    congr 1
    clear Ss
    induction S generalizing v with
    | nil => rfl
    | cons o S ih =>
      simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons]
      rw [entG_opDs hU o v, ih]

/-- **Every snapshot operation's record is among the segments' records**. -/
theorem snap_mem_segsDs (M : WalMarshal) (md : List w8) :
    ∀ (first : Bool) (P : WalHist) (Ss : List WalHist) (m : SnapshotMetadataM) (al : Bool),
      WalOpG.snap m al ∈ Ss.flatten → (snapshotType, M.encSnap m al) ∈ (segsDs M md first P Ss).flatten
  | _, _, [], _, _, h => by cases h
  | first, P, S :: Ss, m, al, h => by
    simp only [segsDs, List.flatten_cons, List.mem_append] at h ⊢
    rcases h with h | h
    · left; right
      exact List.mem_flatMap.2 ⟨_, h, by simp [opDs]⟩
    · right; exact snap_mem_segsDs M md false (P ++ S) Ss m al h

/-- What each record of the segments is: a header record, or one of an operation's. -/
theorem segsDs_mem (M : WalMarshal) (md : List w8) :
    ∀ (first : Bool) (P : WalHist) (Ss : List WalHist),
      ∀ td ∈ (segsDs M md first P Ss).flatten,
        td ∈ hdrDs M md ∨ (∃ hs, td ∈ cutHdrDs M md hs) ∨ ∃ o ∈ Ss.flatten, td ∈ opDs M o
  | _, _, [] => by simp [segsDs]
  | first, P, S :: Ss => by
    intro td htd
    simp only [segsDs, List.flatten_cons, List.mem_append] at htd
    rcases htd with (htd | htd) | htd
    · unfold segHdrDs at htd
      split at htd
      · exact Or.inl htd
      · exact Or.inr (Or.inl ⟨_, htd⟩)
    · obtain ⟨o, ho, h⟩ := List.mem_flatMap.1 htd
      exact Or.inr (Or.inr ⟨o, by simp [ho], h⟩)
    · rcases segsDs_mem M md false (P ++ S) Ss td htd with h | h | ⟨o, ho, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨o, by simp [ho], h⟩)

/-- The snapshot maximum's fold below a bound. -/
theorem snapMax_le : ∀ (P : WalHist) (x X : Nat), x ≤ X →
    (∀ m al, WalOpG.snap m al ∈ P → uint.nat m.Index' ≤ X) →
    P.foldl (fun x o => match o with
      | .save _ _ => x
      | .snap m _ => max x (uint.nat m.Index')) x ≤ X
  | [], _, _, h, _ => h
  | o :: P, x, X, h, hm => by
    simp only [List.foldl_cons]
    apply snapMax_le P _ X _ (fun m al h' => hm m al (List.mem_cons_of_mem _ h'))
    cases o with
    | save _ _ => exact h
    | snap m al => exact Nat.max_le.2 ⟨h, hm m al (List.mem_cons_self ..)⟩

theorem walMaxSnapIdx_append (P Q : WalHist) (X : Nat) (hP : walMaxSnapIdx P ≤ X)
    (hQ : ∀ m al, WalOpG.snap m al ∈ Q → uint.nat m.Index' ≤ X) : walMaxSnapIdx (P ++ Q) ≤ X := by
  unfold walMaxSnapIdx at hP ⊢
  rw [List.foldl_append]
  exact snapMax_le Q _ X hP hQ

/-- The snapshot high-water mark covers both its initial accumulator and every
snapshot index seen by the fold. -/
private theorem snapMax_ge : ∀ (P : WalHist) (x : Nat),
    let y := P.foldl (fun n op => match op with
      | .save _ _ => n
      | .snap m _ => max n (uint.nat m.Index')) x
    x ≤ y ∧ ∀ m al, WalOpG.snap m al ∈ P → uint.nat m.Index' ≤ y
  | [], _ => ⟨Nat.le_refl _, by simp⟩
  | op :: P, x => by
    cases op with
    | save hs es =>
      obtain ⟨hx, hm⟩ := snapMax_ge P x
      exact ⟨hx, fun m al h => hm m al (by simpa using h)⟩
    | snap md a =>
      obtain ⟨hx, hm⟩ := snapMax_ge P (max x (uint.nat md.Index'))
      refine ⟨Nat.le_trans (Nat.le_max_left ..) hx, fun m al h => ?_⟩
      rcases List.mem_cons.1 h with h | h
      · cases h; exact Nat.le_trans (Nat.le_max_right ..) hx
      · exact hm _ _ h

/-- With the current cut naming rule, every snapshot in the skipped prefix is
strictly below the index used for `Open`. Legacy segment names can violate
this inequality, which is why a physical prefix search is needed on upgrade. -/
theorem readAll_prefix_snap_lt {I : WalHist} {k start : Nat}
    (hb : walLastIdx (I.take k) < start) {m : SnapshotMetadataM} {al : Bool}
    (hm : WalOpG.snap m al ∈ I.take k) : uint.nat m.Index' < start := by
  have h : uint.nat m.Index' ≤ walMaxSnapIdx (I.take k) := (snapMax_ge _ 0).2 m al hm
  rw [walLastIdx_eq] at hb
  omega

/-- When the selected segment's name bounds its prefix, the start snapshot
chosen by `ValidSnapshotEntries` survives in the suffix. Index zero can also
be the creation header, which a read starting at the first segment sees. -/
theorem readAll_selected_start {I : WalHist} {k cut : Nat} {s : w64 × w64}
    (hs : walNewestPair (walValidSnaps I cut) = some s)
    (hb : k = 0 ∨ walLastIdx (I.take k) < uint.nat s.1) :
    (k = 0 ∧ cut = 0 ∧ s = (W64 0, W64 0)) ∨
      ∃ m al, WalOpG.snap m al ∈ I.drop k ∧ (m.Index', m.Term') = s := by
  have hm := walNewestPair_mem hs
  unfold walValidSnaps at hm
  rcases List.mem_append.1 hm with h | h
  · by_cases hc : cut = 0
    · simp [hc] at h
      subst s
      exact Or.inl ⟨hb.resolve_right (by simp), hc, rfl⟩
    · simp [hc] at h
  · obtain ⟨op, hop, hp⟩ := List.mem_filterMap.1 h
    cases op with
    | save hs es => cases hp
    | snap m al =>
      change (if uint.nat m.Index' ≤ uint.nat (walLastHS I).Commit' then some (m.Index', m.Term') else none) = some s at hp
      split at hp
      · have he := Option.some.inj hp
        have hall : WalOpG.snap m al ∈ I := List.mem_of_mem_drop hop
        refine Or.inr ⟨m, al, ?_, he⟩
        rcases hb with rfl | hb
        · simpa using hall
        rw [← List.take_append_drop k I] at hall
        rcases List.mem_append.1 hall with hpre | hpost
        · have ha := readAll_prefix_snap_lt hb hpre
          rw [← he] at ha
          exact absurd ha (Nat.lt_irrefl _)
        · exact hpost
      · cases hp

/-- The indices' fold below a bound `B` when every index read is. -/
theorem raIdxT_lt (U : WalUnmarshal) (s : w64 × w64) (B : Nat) :
    ∀ (L : List (w64 × List w8)) (ix : w64 × w64),
      (∀ td ∈ L, td.1 = entryType → ∀ e, U.decEntry td.2 = some e → uint.nat e.Index' < B) →
      (∀ td ∈ L, td.1 = snapshotType → ∀ p, U.decSnap td.2 = some p → uint.nat p.1 < B) →
      uint.nat ix.1 < B → uint.nat ix.2 < B →
      uint.nat (L.foldl (raIdxT U s) ix).1 < B ∧ uint.nat (L.foldl (raIdxT U s) ix).2 < B
  | [], _, _, _, h1, h2 => ⟨h1, h2⟩
  | td :: L, ix, he, hs, h1, h2 => by
    simp only [List.foldl_cons]
    apply raIdxT_lt U s B L _ (fun td' h' => he td' (List.mem_cons_of_mem _ h'))
      (fun td' h' => hs td' (List.mem_cons_of_mem _ h'))
    · unfold raIdxT raIdx
      simp only
      split
      · rename_i hte
        cases hd : U.decEntry td.2 with
        | none => exact h1
        | some e => exact he td (List.mem_cons_self ..) hte e hd
      · split
        · rename_i _ hts
          cases hd : U.decSnap td.2 with
          | none => exact h1
          | some p =>
            have := hs td (List.mem_cons_self ..) hts p hd
            simp only; split <;> omega
        · exact h1
    · unfold raIdxT raIdx
      simp only
      split
      · split <;> exact h2
      · split
        · rename_i _ hts
          cases hd : U.decSnap td.2 with
          | none => exact h2
          | some p =>
            have := hs td (List.mem_cons_self ..) hts p hd
            simp only; split <;> omega
        · exact h2

/-- **The history's indices below `w.enti`/`w.snapi`** (see the file header): the records read are
those of the segments `Ss` after the operations `P` (`I = P ++ Ss.flatten`), `P`'s indices below
`w.snapi`. With no index `2^64 - 1` in `I`, the maximum plus one does not wrap. -/
theorem readAll_idxD {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M) (md : List w8)
    (s : w64 × w64) (first : Bool) (P : WalHist) (Ss : List WalHist) (I : WalHist)
    (hI : I = P ++ Ss.flatten)
    (ix : w64 × w64) (hix : (segsDs M md first P Ss).flatten.foldl (raIdxT U s) (W64 0, W64 0) = ix)
    (hP : walLastIdx P ≤ uint.nat ix.2) :
    (walLastIdx I ≤ max (uint.nat ix.1) (uint.nat ix.2) ∧ walMaxSnapIdx I ≤ uint.nat ix.2) ∧
      (¬ walHasMaxIdx I → max (uint.nat ix.1) (uint.nat ix.2) + 1 < 2 ^ 64) := by
  generalize hD : (segsDs M md first P Ss).flatten = D at hix
  have hsn := raIdxT_snap_le U s D (W64 0, W64 0)
  rw [hix] at hsn
  have hsnap : ∀ m al, WalOpG.snap m al ∈ Ss.flatten → uint.nat m.Index' ≤ uint.nat ix.2 := by
    intro m al hm
    have hmem := snap_mem_segsDs M md first P Ss m al hm
    rw [hD] at hmem
    exact hsn.2 _ hmem rfl _ (hU.snap m al)
  have hms : walMaxSnapIdx I ≤ uint.nat ix.2 := by
    rw [hI]
    apply walMaxSnapIdx_append P _ _ _ hsnap
    rw [walLastIdx_snap] at hP
    exact Nat.le_trans (Nat.le_max_right _ _) hP
  refine ⟨⟨?_, hms⟩, ?_⟩
  · rw [walLastIdx_eq]
    refine Nat.max_le.2 ⟨?_, Nat.le_trans hms (Nat.le_max_right _ _)⟩
    rw [hI, List.foldl_append, ← segsDs_entG hU md first P Ss, hD]
    have h1 := entG_start U D (P.foldl lastEntF 0) 0
    have h2 := entG_le U s D (W64 0, W64 0) 0 (Nat.zero_le _)
    rw [hix] at h2
    have h3 : P.foldl lastEntF 0 ≤ walLastIdx P := by rw [walLastIdx_eq]; exact Nat.le_max_left _ _
    omega
  · intro hnm
    have hB := raIdxT_lt U s (2 ^ 64 - 1) D (W64 0, W64 0) ?_ ?_ (by simp) (by simp)
    · rw [hix] at hB
      have : uint.nat ix.1 < 2 ^ 64 - 1 := hB.1
      have : uint.nat ix.2 < 2 ^ 64 - 1 := hB.2
      omega
    · intro td htd ht e he
      rw [← hD] at htd
      rcases segsDs_mem M md first P Ss td htd with h | ⟨hs, h⟩ | ⟨o, ho, h⟩
      · simp only [hdrDs, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl <;> exact absurd ht (by simp [entryType, stateType, snapshotType, metadataType, crcType])
      · simp only [cutHdrDs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with (rfl | rfl) | h
        · exact absurd ht (by simp [entryType, stateType, snapshotType, metadataType, crcType])
        · exact absurd ht (by simp [entryType, stateType, snapshotType, metadataType, crcType])
        · split at h
          · cases h
          · simp only [List.mem_singleton] at h; subst h; exact absurd ht (by simp [entryType, stateType, snapshotType, metadataType, crcType])
      · cases o with
        | save hs es =>
          simp only [opDs, List.mem_append, List.mem_map] at h
          rcases h with ⟨e', he', rfl⟩ | h
          · rw [hU.entry e'] at he
            have he2 := Option.some.inj he
            subst he2
            have hidx : uint.nat e'.Index' ≠ 2 ^ 64 - 1 := fun h =>
              hnm ⟨WalOpG.save hs es, by rw [hI]; exact List.mem_append_right _ ho, e', he', h⟩
            have : uint.nat e'.Index' < 2 ^ 64 := (show uint.nat e'.Index' < 2 ^ 64 from e'.Index'.isLt)
            omega
          · split at h
            · cases h
            · simp only [List.mem_singleton] at h; subst h; exact absurd ht (by simp [entryType, stateType, snapshotType, metadataType, crcType])
        | snap m al =>
          simp only [opDs, List.mem_singleton] at h; subst h; exact absurd ht (by simp [entryType, stateType, snapshotType, metadataType, crcType])
    · intro td htd ht p hp
      rw [← hD] at htd
      rcases segsDs_mem M md first P Ss td htd with h | ⟨hs, h⟩ | ⟨o, ho, h⟩
      · simp only [hdrDs, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl
        · exact absurd ht (by simp [entryType, stateType, snapshotType, metadataType, crcType])
        · exact absurd ht (by simp [entryType, stateType, snapshotType, metadataType, crcType])
        · rw [hU.snap0] at hp; cases hp; simp
      · simp only [cutHdrDs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with (rfl | rfl) | h
        · exact absurd ht (by simp [entryType, stateType, snapshotType, metadataType, crcType])
        · exact absurd ht (by simp [entryType, stateType, snapshotType, metadataType, crcType])
        · split at h
          · cases h
          · simp only [List.mem_singleton] at h; subst h; exact absurd ht (by simp [entryType, stateType, snapshotType, metadataType, crcType])
      · cases o with
        | save hs es =>
          simp only [opDs, List.mem_append, List.mem_map] at h
          rcases h with ⟨e', -, rfl⟩ | h
          · exact absurd ht (by simp [entryType, stateType, snapshotType, metadataType, crcType])
          · split at h
            · cases h
            · simp only [List.mem_singleton] at h; subst h; exact absurd ht (by simp [entryType, stateType, snapshotType, metadataType, crcType])
        | snap m al =>
          simp only [opDs, List.mem_singleton] at h
          subst h
          rw [hU.snap m] at hp
          cases hp
          have hidx : uint.nat m.Index' ≠ 2 ^ 64 - 1 := fun h =>
            hnm ⟨WalOpG.snap m al, by rw [hI]; exact List.mem_append_right _ ho, h⟩
          have : uint.nat m.Index' < 2 ^ 64 := (show uint.nat m.Index' < 2 ^ 64 from m.Index'.isLt)
          simp only
          omega

private theorem raStep_keeps_match {U : WalUnmarshal} {s : w64 × w64} {st st' : RAState}
    {td : w64 × List w8} (h : raStep U s st td = .ok st') (hm : st.matched = true) :
    st'.matched = true := by
  unfold raStep at h
  repeat' first | split at h | contradiction
  all_goals cases h <;> first | exact hm | rfl

/-- A successful read through a matching record remembers that match until EOF. -/
theorem raFold_match {U : WalUnmarshal} {s : w64 × w64} (ds : List (w64 × List w8))
    {st0 st : RAState} (hf : ds.foldlM (raStep U s) st0 = .ok st)
    (hm : st0.matched = true ∨ ∃ bytes, (snapshotType, bytes) ∈ ds ∧ U.decSnap bytes = some s) :
    st.matched = true := by
  induction ds generalizing st0 with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hf
    subst st; simpa using hm
  | cons td ds ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at hf
    cases h : raStep U s st0 td with
    | error e => rw [h] at hf; cases hf
    | ok st1 =>
      rw [h] at hf
      apply ih hf
      rcases hm with hm | ⟨bytes, hb, hd⟩
      · exact Or.inl (raStep_keeps_match h hm)
      rcases List.mem_cons.1 hb with ht | hb
      · subst td
        simp [raStep, snapshotType, entryType, stateType, metadataType, crcType, hd] at h
        subst st1; exact Or.inl rfl
      · exact Or.inr ⟨bytes, hb, hd⟩

/-- **A matched start has its snapshot record among those read** (`raStep`'s only `matched := true`). -/
theorem raStep_matched (U : WalUnmarshal) (s : w64 × w64) :
    ∀ (L : List (w64 × List w8)) (st0 st : RAState), L.foldlM (raStep U s) st0 = .ok st →
      st0.matched = false → st.matched = true →
      ∃ td ∈ L, td.1 = snapshotType ∧ ∃ p, U.decSnap td.2 = some p ∧ p.1 = s.1
  | [], st0, st, h, h0, h1 => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rw [h0] at h1; cases h1
  | td :: L, st0, st, h, h0, h1 => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases hst : raStep U s st0 td with
    | error e => rw [hst] at h; cases h
    | ok st1 =>
      rw [hst] at h
      by_cases hm : st1.matched = true
      · -- the step set it
        refine ⟨td, List.mem_cons_self .., ?_⟩
        unfold raStep at hst
        split at hst
        · split at hst
          · cases hst
          · split at hst
            · cases hst
            · cases hst; simp [h0] at hm
        · split at hst
          · split at hst
            · cases hst
            · cases hst; simp [h0] at hm
          · split at hst
            · split at hst
              · split at hst
                · cases hst; simp [h0] at hm
                · cases hst
              · cases hst; simp [h0] at hm
            · split at hst
              · cases hst; simp [h0] at hm
              · split at hst
                · rename_i hts
                  split at hst
                  · cases hst
                  · rename_i p hp
                    split at hst
                    · rename_i hps
                      exact ⟨hts, p, hp, hps⟩
                    · cases hst; simp [h0] at hm
                · cases hst
      · obtain ⟨td', h', rest⟩ := raStep_matched U s L st1 st h (by simpa using hm) h1
        exact ⟨td', List.mem_cons_of_mem _ h', rest⟩

/-- **`ReadAll`'s indices after the loop** (obligation (d) of `walOpenWF`): the loop read the WAL's
records from its segment `kk` (`g`, named at most the start's index, `hsel`) on, and matched the
start; then the history's `walLastIdx`/`walMaxSnapIdx` are below `w.enti`/`w.snapi` (the operations
before the segment by its name bound, `WalAbsD.nameBound`, below the start's index, which the matched
snapshot record raised `w.snapi` to), and with no index `2^64 - 1` in the history the maximum plus one
does not wrap. -/
theorem readAll_idx {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {U : WalUnmarshal} (hU : U.Ok Mr)
    {d : WalDur} {lay : WalLay} {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (kk : Nat) (g : SegG)
    (hg : lay.segs[kk]? = some g) (s : w64 × w64)
    (hsel : ∀ sq ix, g.name = walFileName sq ix → ix < 2 ^ 64 → ix ≤ uint.nat s.1)
    {acc : List WalRec} (hacc : (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts)).drop
      (recsOfSegs C Mr d.metadata ((segsOf (histM d) lay.cuts).take (lay.first + kk))).length = acc)
    {st : RAState} (hf : (acc.map (fun r => (r.typ, r.data))).foldlM (raStep U s) raInit = .ok st)
    (hm : st.matched = true) {ix : w64 × w64} (hix : acc.foldl (raIdx U s) (W64 0, W64 0) = ix) :
    (walLastIdx (histM d) ≤ max (uint.nat ix.1) (uint.nat ix.2) ∧
        walMaxSnapIdx (histM d) ≤ uint.nat ix.2) ∧
      (¬ walHasMaxIdx (histM d) → max (uint.nat ix.1) (uint.nat ix.2) + 1 < 2 ^ 64) := by
  have hkk : kk < lay.segs.length := (List.getElem?_eq_some_iff.1 hg).1
  obtain ⟨hcp, hlt, hfl⟩ := hab.cuts
  have hle : ∀ b ∈ lay.cuts, b ≤ (histM d).length := fun b hb => cut_le_length (hcp b hb)
  have hp : lay.first + kk ≤ lay.cuts.length := by omega
  have hk := length_flatten_take_segsOf (I := histM d) hlt hle hp
  have hflat : (segsOf (histM d) lay.cuts).flatten = histM d :=
    segsOf_flatten _ _ (hlt.imp Nat.le_of_lt) hle
  rw [foldl_raIdx_map] at hix
  -- the matched start's snapshot record among those read
  obtain ⟨tds, htds, hts, pm, hpm, hpms⟩ :=
    raStep_matched U s _ raInit st hf rfl hm
  generalize hSs : segsOf (histM d) lay.cuts = Ss at hk hflat hacc
  generalize hpp : lay.first + kk = p at hk hp hacc
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · subst h0
    have hmap : acc.map (fun r => (r.typ, r.data)) = (segsDs Mr d.metadata true [] Ss).flatten := by
      rw [← hacc]
      simp only [List.take_zero]
      have e0 : (recsOfSegs C Mr d.metadata []).length = 0 := rfl
      rw [e0, List.drop_zero, recsOfSegs_map]
    rw [hmap] at hix
    refine readAll_idxD hU d.metadata s true [] Ss (histM d) (by rw [← hflat]; rfl) ix hix ?_
    show walLastIdx [] ≤ _
    exact Nat.zero_le _
  · have hpre : Ss.take p ≠ [] := by
      intro h
      rw [List.take_eq_nil_iff] at h
      rcases h with h | h
      · omega
      · subst h; simp [segsOf] at hSs
    have hmap : acc.map (fun r => (r.typ, r.data)) =
        (segsDs Mr d.metadata false (Ss.take p).flatten (Ss.drop p)).flatten := by
      rw [← hacc]
      have := recsOfSegs_drop_map C Mr d.metadata hpre (Ss.drop p)
      rw [List.take_append_drop] at this
      exact this
    have hI : histM d = (Ss.take p).flatten ++ (Ss.drop p).flatten := by
      rw [← hflat, ← List.flatten_append, List.take_append_drop]
    have hP : (Ss.take p).flatten = (histM d).take (segStart lay.cuts p) := by
      rw [← hk, hI, List.take_left]
    rw [hmap] at hix htds
    refine readAll_idxD hU d.metadata s false _ (Ss.drop p) (histM d) hI ix hix ?_
    obtain ⟨sq, ixn, hnm, hixn, hnb⟩ := hab.nameBound kk g hg
    rw [hpp] at hnb
    have h1 := hnb h0
    have h2 := hsel sq ixn hnm hixn
    have h3 := (raIdxT_snap_le U s _ (W64 0, W64 0)).2 tds htds hts pm hpm
    rw [hix] at h3
    rw [hP]
    rw [hpms] at h3
    omega

/-- A read of all the filename-selected segments of a WAL written with the
current naming rule matches the requested valid snapshot before EOF. -/
theorem readAll_eof_matched {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {U : WalUnmarshal} (hU : U.Ok Mr)
    {d : WalDur} {lay : WalLay} {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (kk : Nat) (g : SegG)
    (hg : lay.segs[kk]? = some g) (s : w64 × w64)
    (hsel : ∀ sq ix, g.name = walFileName sq ix → ix < 2 ^ 64 → ix ≤ uint.nat s.1)
    {acc : List WalRec} (hacc : (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts)).drop
      (recsOfSegs C Mr d.metadata ((segsOf (histM d) lay.cuts).take (lay.first + kk))).length = acc)
    {st : RAState} (hf : (acc.map (fun r => (r.typ, r.data))).foldlM (raStep U s) raInit = .ok st)
    (hs : walNewestPair (walValidSnaps (histM d) d.cut) = some s) : st.matched = true := by
  apply raFold_match _ hf
  right
  have hkk : kk < lay.segs.length := (List.getElem?_eq_some_iff.1 hg).1
  obtain ⟨hcp, hlt, hfl⟩ := hab.cuts
  have hle : ∀ b ∈ lay.cuts, b ≤ (histM d).length := fun b hb => cut_le_length (hcp b hb)
  have hp : lay.first + kk ≤ lay.cuts.length := by omega
  have hk := length_flatten_take_segsOf (I := histM d) hlt hle hp
  have hflat : (segsOf (histM d) lay.cuts).flatten = histM d :=
    segsOf_flatten _ _ (hlt.imp Nat.le_of_lt) hle
  generalize hSs : segsOf (histM d) lay.cuts = Ss at hk hflat hacc
  generalize hpp : lay.first + kk = p at hk hp hacc
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · subst h0
    have hmap : acc.map (fun r => (r.typ, r.data)) = (segsDs Mr d.metadata true [] Ss).flatten := by
      rw [← hacc]
      simp only [List.take_zero]
      have e0 : (recsOfSegs C Mr d.metadata []).length = 0 := rfl
      rw [e0, List.drop_zero, recsOfSegs_map]
    rw [hmap]
    rcases readAll_selected_start (k := 0) hs (Or.inl rfl) with ⟨-, -, rfl⟩ | ⟨m, al, hm, he⟩
    · refine ⟨Mr.snap0, ?_, hU.snap0⟩
      cases Ss with
      | nil => simp [segsOf] at hSs
      | cons S Ss => simp [segsDs, segHdrDs, hdrDs]
    · refine ⟨Mr.encSnap m al, snap_mem_segsDs Mr d.metadata true [] Ss m al ?_, ?_⟩
      · simpa [hflat] using hm
      · rw [hU.snap m al, he]
  · have hpre : Ss.take p ≠ [] := by
      intro h
      rw [List.take_eq_nil_iff] at h
      rcases h with h | h
      · omega
      · subst h; simp [segsOf] at hSs
    have hmap : acc.map (fun r => (r.typ, r.data)) =
        (segsDs Mr d.metadata false (Ss.take p).flatten (Ss.drop p)).flatten := by
      rw [← hacc]
      have := recsOfSegs_drop_map C Mr d.metadata hpre (Ss.drop p)
      rw [List.take_append_drop] at this
      exact this
    have hI : histM d = (Ss.take p).flatten ++ (Ss.drop p).flatten := by
      rw [← hflat, ← List.flatten_append, List.take_append_drop]
    have hP : (Ss.take p).flatten = (histM d).take (segStart lay.cuts p) := by
      rw [← hk, hI, List.take_left]
    obtain ⟨sq, ix, hname, hix, hbound⟩ := hab.nameBound kk g hg
    rw [hpp] at hbound
    have hb := hbound h0
    have hi := hsel sq ix hname hix
    have hb' : walLastIdx ((histM d).take (segStart lay.cuts p)) < uint.nat s.1 := by omega
    rcases readAll_selected_start hs (Or.inr hb') with ⟨-, -, he⟩ | ⟨m, al, hm, he⟩
    · rw [he] at hb'; simp at hb'
    · rw [hmap]
      refine ⟨Mr.encSnap m al, snap_mem_segsDs Mr d.metadata false _ _ m al ?_, ?_⟩
      · rw [← hk, hI, List.drop_left] at hm
        exact hm
      · rw [hU.snap m al, he]

end pure

end WalFs
end EtcdGrove
end Perennial

end
