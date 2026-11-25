/- Lean-first (no Rocq counterpart).

# `ReadAll`'s loop with the pending entries (P6 E3, the torn-`Save` fix; `notes/wal-p6-handoff.md`)

Since the fork's `2bd3048d7`, `readAll` holds the entry records it decodes in `pending` and applies
them (the old entry arm, unchanged) when any later record arrives; the entry records no record follows
are dropped. `raStepP` is one iteration over the loop's variables and `pending`; `readAllFoldP` the
whole read (the stop check and the match as `readAllFold`'s, `pending` ignored).

`readAllFoldP_append`: over the records of a read ending in a non-entry record (every WAL history's,
whose last record is a header's or an operation's last: a `Save` with entries ends with its state
record), followed by a run of entry records that decode (a torn `Save`'s), the read is `readAllFold`'s
over the former alone.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncFold

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalEnc

open go_etcd_io.raft.v3

section pend
variable [GooseExts]

/-- The pending entries applied (the old entry arm on each, in order). -/
def flushP (s : w64 × w64) (ents pend : List EntryM) : Except ReadAllErr (List EntryM) :=
  match pend.foldlM (fun ents e => readEnt (uint.nat s.1) ents e) ents with
  | none => .error .sliceOutOfRange
  | some x => .ok x

/-- **One iteration of the loop with `pending`** (S/wal.go:570-678 at `2bd3048d7`): an entry record is
decoded (`MustUnmarshalEntry`) and appended to `pending`; any other record first applies `pending`
(`flushP`), then takes its arm (`raStep`'s). -/
def raStepP (U : WalUnmarshal) (s : w64 × w64) (sp : RAState × List EntryM) (r : w64 × List w8) :
    Except ReadAllErr (RAState × List EntryM) :=
  if r.1 = entryType then
    match U.decEntry r.2 with
    | none => .error .panic
    | some e => .ok (sp.1, sp.2 ++ [e])
  else
    match flushP s sp.1.ents sp.2 with
    | .error x => .error x
    | .ok ents =>
      match raStep U s { sp.1 with ents := ents } r with
      | .error x => .error x
      | .ok st => .ok (st, [])

/-- **`ReadAll`'s result with `pending`** (as `readAllFold`; the pending entries ignored). -/
def readAllFoldP (U : WalUnmarshal) (s : w64 × w64) (write : Bool) (recs : List WalRec)
    (stop : WalStop) : Except ReadAllErr (List w8 × HardStateM × List EntryM) :=
  (recs.map (fun r => (r.typ, r.data))).foldlM (raStepP U s) (raInit, []) >>= fun sp =>
  if (if write then stop ≠ .eof else stop ≠ .eof ∧ stop.unexpectedEOF = false) then
    .error (.stop stop)
  else if sp.1.matched = false then .error .snapshotNotFound
  else .ok (sp.1.md.getD [], sp.1.hs, sp.1.ents)

/-- The entry arm of `raStep` is `readEnt` after the decode. -/
theorem raStep_entry_eq {U : WalUnmarshal} {s : w64 × w64} {st : RAState} {d : List w8} {e : EntryM}
    (he : U.decEntry d = some e) :
    raStep U s st (entryType, d) = match readEnt (uint.nat s.1) st.ents e with
      | none => .error .sliceOutOfRange
      | some ents => .ok { st with ents := ents } := by
  simp [raStep, he]; rfl

/-- Applying the pending entries one more. -/
theorem flushP_snoc (s : w64 × w64) (ents pend : List EntryM) (e : EntryM) :
    flushP s ents (pend ++ [e]) = (flushP s ents pend >>= fun x =>
      match readEnt (uint.nat s.1) x e with
      | none => .error .sliceOutOfRange
      | some y => .ok y) := by
  unfold flushP
  rw [List.foldlM_append]
  cases h : pend.foldlM (fun ents e => readEnt (uint.nat s.1) ents e) ents with
  | none => rfl
  | some x =>
    cases hr : readEnt (uint.nat s.1) x e <;>
      simp [hr, Option.bind, pure, bind, Except.bind, List.foldlM_cons, List.foldlM_nil]

/-- The records' entry records decode. -/
def EntsDecode (U : WalUnmarshal) (ds : List (w64 × List w8)) : Prop :=
  ∀ r ∈ ds, r.1 = entryType → ∃ e, U.decEntry r.2 = some e

/-- **The loop with `pending` over records ending in a non-entry record** is the old loop from the
pending entries applied, with nothing pending after (`pend = []` when there are no records). -/
theorem foldlM_raStepP_eq (U : WalUnmarshal) (s : w64 × w64) :
    ∀ (ds : List (w64 × List w8)) (st : RAState) (pend : List EntryM),
    EntsDecode U ds → (∀ r ∈ ds.getLast?, r.1 ≠ entryType) → (ds = [] → pend = []) →
    ds.foldlM (raStepP U s) (st, pend) =
      ((flushP s st.ents pend >>= fun ents => ds.foldlM (raStep U s) { st with ents := ents }) >>=
        fun st' => .ok (st', [])) := by
  intro ds
  induction ds with
  | nil =>
    intro st pend _ _ hp
    rw [hp rfl]
    simp [flushP, List.foldlM_nil]
    rfl
  | cons r ds ih =>
    intro st pend hdec hlast _
    have hdec' : EntsDecode U ds := fun x hx => hdec x (List.mem_cons_of_mem _ hx)
    by_cases hr : r.1 = entryType
    · obtain ⟨e, he⟩ := hdec r List.mem_cons_self hr
      have hne : ds ≠ [] := by
        rintro rfl; exact hlast r (by simp) hr
      have hlast' : ∀ x ∈ ds.getLast?, x.1 ≠ entryType := by
        intro x hx; apply hlast x
        rw [List.getLast?_cons, Option.mem_def, hx]; rfl
      have hstep : raStepP U s (st, pend) r = .ok (st, pend ++ [e]) := by
        simp [raStepP, hr, he]
      rw [List.foldlM_cons, hstep]
      show List.foldlM (raStepP U s) (st, pend ++ [e]) ds = _
      rw [ih st (pend ++ [e]) hdec' hlast' (fun h => absurd h hne), flushP_snoc]
      have hraw : ∀ ents, raStep U s { st with ents := ents } r = match readEnt (uint.nat s.1) ents e with
          | none => .error .sliceOutOfRange
          | some y => .ok { st with ents := y } := by
        intro ents
        obtain ⟨t, d⟩ := r
        simp only at hr he; subst hr
        exact raStep_entry_eq he
      cases hf : flushP s st.ents pend with
      | error x => rfl
      | ok ents =>
        simp only [except_ok_bind, List.foldlM_cons, hraw]
        cases readEnt (uint.nat s.1) ents e <;> rfl
    · have hstep : raStepP U s (st, pend) r =
          ((flushP s st.ents pend >>= fun ents => raStep U s { st with ents := ents } r) >>=
            fun st' => .ok (st', [])) := by
        simp only [raStepP, hr, ↓reduceIte]
        cases flushP s st.ents pend with
        | error x => rfl
        | ok ents =>
          simp only [except_ok_bind]
          cases raStep U s { st with ents := ents } r <;> rfl
      rw [List.foldlM_cons, hstep]
      cases hf : flushP s st.ents pend with
      | error x => rfl
      | ok ents =>
        simp only [except_ok_bind, List.foldlM_cons]
        cases hs : raStep U s { st with ents := ents } r with
        | error x => rfl
        | ok st1 =>
          simp only [except_ok_bind]
          by_cases hds : ds = []
          · subst hds; rfl
          · have hlast' : ∀ x ∈ ds.getLast?, x.1 ≠ entryType := by
              intro x hx; apply hlast x
              rw [List.getLast?_cons, Option.mem_def, hx]; rfl
            rw [ih st1 [] hdec' hlast' (fun _ => rfl)]
            simp [flushP]
            rfl

/-- **A run of decodable entry records** adds their entries to `pending`. -/
theorem foldlM_raStepP_ents (U : WalUnmarshal) (s : w64 × w64) :
    ∀ (ds : List (w64 × List w8)) (st : RAState) (pend : List EntryM),
    EntsDecode U ds → (∀ r ∈ ds, r.1 = entryType) →
    ∃ es, ds.foldlM (raStepP U s) (st, pend) = .ok (st, pend ++ es) := by
  intro ds
  induction ds with
  | nil => intro st pend _ _; exact ⟨[], by simp; rfl⟩
  | cons r ds ih =>
    intro st pend hdec hall
    have hr := hall r List.mem_cons_self
    obtain ⟨e, he⟩ := hdec r List.mem_cons_self hr
    obtain ⟨es, hes⟩ := ih st (pend ++ [e]) (fun x hx => hdec x (List.mem_cons_of_mem _ hx))
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    refine ⟨e :: es, ?_⟩
    have hstep : raStepP U s (st, pend) r = .ok (st, pend ++ [e]) := by
      simp [raStepP, hr, he]
    rw [List.foldlM_cons, hstep]
    show List.foldlM (raStepP U s) (st, pend ++ [e]) ds = _
    rw [hes]; simp

/-- **`ReadAll` with `pending` over a history's records and a torn run of entry records**: records
`recs` ending in a non-entry record (or none), followed by entry records `ps`, all decoding, give the
old read of `recs`. -/
theorem readAllFoldP_append (U : WalUnmarshal) (s : w64 × w64) (write : Bool) (recs ps : List WalRec)
    (stop : WalStop) (hdec : EntsDecode U ((recs ++ ps).map (fun r => (r.typ, r.data))))
    (hlast : ∀ r ∈ recs.getLast?, r.typ ≠ entryType) (hps : ∀ r ∈ ps, r.typ = entryType) :
    readAllFoldP U s write (recs ++ ps) stop = readAllFold U s write recs stop := by
  unfold readAllFoldP readAllFold
  rw [List.map_append, List.foldlM_append]
  have hd1 : EntsDecode U (recs.map (fun r => (r.typ, r.data))) := fun x hx =>
    hdec x (by rw [List.map_append]; exact List.mem_append_left _ hx)
  have hd2 : EntsDecode U (ps.map (fun r => (r.typ, r.data))) := fun x hx =>
    hdec x (by rw [List.map_append]; exact List.mem_append_right _ hx)
  have hl : ∀ x ∈ (recs.map (fun r => (r.typ, r.data))).getLast?, x.1 ≠ entryType := by
    intro x hx
    rw [List.getLast?_map, Option.mem_def, Option.map_eq_some_iff] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact hlast r hr
  rw [foldlM_raStepP_eq U s _ raInit [] hd1 hl (fun _ => rfl)]
  have hf0 : flushP s raInit.ents [] = .ok raInit.ents := by simp [flushP]
  rw [hf0]
  simp only [except_ok_bind]
  have hri : ({ raInit with ents := raInit.ents } : RAState) = raInit := rfl
  rw [hri]
  cases (recs.map (fun r => (r.typ, r.data))).foldlM (raStep U s) raInit with
  | error x => rfl
  | ok st =>
    simp only [except_ok_bind]
    obtain ⟨es, hes⟩ := foldlM_raStepP_ents U s _ st [] hd2 (by
      intro x hx; rw [List.mem_map] at hx; obtain ⟨r, hr, rfl⟩ := hx; exact hps r hr)
    rw [hes]
    rfl

/-! ## The WAL's records end with a non-entry record; its entry records decode -/

/-- The last record of `D`, if any, is not an entry record. -/
def NoEntLast (D : List (w64 × List w8)) : Prop := ∀ x ∈ D.getLast?, x.1 ≠ entryType

theorem noEntLast_append {A B : List (w64 × List w8)} (hA : NoEntLast A) (hB : NoEntLast B) :
    NoEntLast (A ++ B) := by
  intro x hx
  rw [List.getLast?_append] at hx
  cases hb : B.getLast? with
  | none => rw [hb] at hx; exact hA x (by simpa using hx)
  | some y =>
    rw [hb, Option.some_or, Option.mem_def, Option.some.injEq] at hx
    subst hx; exact hB _ hb

theorem stateType_ne_entry : stateType ≠ entryType := by unfold stateType entryType; decide
theorem snapshotType_ne_entry : snapshotType ≠ entryType := by unfold snapshotType entryType; decide
theorem metadataType_ne_entry : metadataType ≠ entryType := by unfold metadataType entryType; decide
theorem crcType_ne_entry : crcType ≠ entryType := by unfold crcType entryType; decide

theorem noEntLast_last {D : List (w64 × List w8)} {a : w64 × List w8} (h : D.getLast? = some a)
    (ha : a.1 ≠ entryType) : NoEntLast D := by
  intro x hx
  rw [h, Option.mem_def, Option.some.injEq] at hx
  subst hx; exact ha

theorem noEntLast_opDs (M : WalMarshal) (o : WalOp) : NoEntLast (opDs M o) := by
  cases o with
  | save h es =>
    simp only [opDs]
    by_cases hc : es = [] ∧ hsEmptyP h
    · rw [if_pos hc, hc.1]; intro x hx; simp at hx
    · rw [if_neg hc]
      exact noEntLast_last (a := (stateType, M.encState h)) (by simp) stateType_ne_entry
  | snap m al =>
    exact noEntLast_last (a := (snapshotType, M.encSnap m al)) (by simp only [opDs]; rfl)
      snapshotType_ne_entry

theorem noEntLast_flatMap (M : WalMarshal) (S : WalHist) : NoEntLast (S.flatMap (opDs M)) := by
  induction S with
  | nil => intro x hx; simp at hx
  | cons o S ih => rw [List.flatMap_cons]; exact noEntLast_append (noEntLast_opDs M o) ih

theorem noEntLast_segHdr (M : WalMarshal) (md : List w8) (first : Bool) (P : WalHist) :
    NoEntLast (segHdrDs M md first P) := by
  unfold segHdrDs
  cases first
  · simp only [Bool.false_eq_true, ite_false, cutHdrDs]
    split
    · exact noEntLast_last (a := (metadataType, md)) (by simp) metadataType_ne_entry
    · exact noEntLast_last (a := (stateType, M.encState (walLastHS P))) (by simp) stateType_ne_entry
  · simp only [ite_true, hdrDs]
    exact noEntLast_last (a := (snapshotType, M.snap0)) (by simp) snapshotType_ne_entry

theorem noEntLast_segsDs (M : WalMarshal) (md : List w8) :
    ∀ (first : Bool) (P : WalHist) (Ss : List WalHist), NoEntLast (segsDs M md first P Ss).flatten
  | _, _, [] => by intro x hx; simp [segsDs] at hx
  | first, P, S :: Ss => by
    simp only [segsDs, List.flatten_cons]
    exact noEntLast_append (noEntLast_append (noEntLast_segHdr M md first P) (noEntLast_flatMap M S))
      (noEntLast_segsDs M md false (P ++ S) Ss)

theorem noEntLast_drop {D : List (w64 × List w8)} (h : NoEntLast D) (n : Nat) :
    NoEntLast (D.drop n) := by
  intro x hx
  rw [List.getLast?_drop] at hx
  split at hx
  · simp at hx
  · exact h x hx

/-- Every entry record of the operations' records is an encoded entry. -/
def EntsEnc (M : WalMarshal) (D : List (w64 × List w8)) : Prop :=
  ∀ p ∈ D, p.1 = entryType → ∃ e, p.2 = M.encEntry e

theorem entsEnc_segsDs (M : WalMarshal) (md : List w8) :
    ∀ (first : Bool) (P : WalHist) (Ss : List WalHist), EntsEnc M (segsDs M md first P Ss).flatten
  | _, _, [] => by intro p hp; simp [segsDs] at hp
  | first, P, S :: Ss => by
    intro p hp hpt
    simp only [segsDs, List.flatten_cons, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exfalso
      have hne : p.1 = crcType ∨ p.1 = metadataType ∨ p.1 = snapshotType ∨ p.1 = stateType := by
        unfold segHdrDs at hp
        cases first
        · simp only [Bool.false_eq_true, ite_false, cutHdrDs, List.mem_append] at hp
          rcases hp with hp | hp
          · simp at hp; rcases hp with rfl | rfl <;> simp
          · split at hp
            · simp at hp
            · simp at hp; subst hp; simp
        · simp only [ite_true, hdrDs] at hp
          simp at hp; rcases hp with rfl | rfl | rfl <;> simp
      rcases hne with h | h | h | h <;> rw [h] at hpt
      · exact crcType_ne_entry hpt
      · exact metadataType_ne_entry hpt
      · exact snapshotType_ne_entry hpt
      · exact stateType_ne_entry hpt
    · obtain ⟨o, -, ho⟩ := List.mem_flatMap.1 hp
      cases o with
      | save h es =>
        simp only [opDs, List.mem_append] at ho
        rcases ho with ho | ho
        · obtain ⟨e, -, rfl⟩ := List.mem_map.1 ho; exact ⟨e, rfl⟩
        · split at ho
          · simp at ho
          · simp at ho; subst ho; exact absurd hpt stateType_ne_entry
      | snap m al => simp [opDs] at ho; subst ho; exact absurd hpt snapshotType_ne_entry
    · exact entsEnc_segsDs M md false (P ++ S) Ss p hp hpt

theorem entsDecode_of_enc {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M)
    {D : List (w64 × List w8)} (h : EntsEnc M D) : EntsDecode U D := by
  intro r hr ht
  obtain ⟨e, he⟩ := h r hr ht
  exact ⟨e, by rw [he, hU.entry]⟩

/-- **`ReadAll` with `pending` on the WAL's records from some position on, then a torn `Save`'s
entry records**: the old fold on the WAL's records. -/
theorem readAllFoldP_wal {C : WalCodec} {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M)
    (s : w64 × w64) (write : Bool) (md : List w8) (Ss : List WalHist) (n : Nat) (c : w32)
    (es : List EntryM) (stop : WalStop) :
    readAllFoldP U s write ((recsOfSegs C M md Ss).drop n ++ chainRecs C c (pendDs M es)) stop =
      readAllFold U s write ((recsOfSegs C M md Ss).drop n) stop := by
  have hmap : ∀ c D, (chainRecs C c D).map (fun r => (r.typ, r.data)) = D := chainRecs_map C
  apply readAllFoldP_append
  · rw [List.map_append, List.map_drop, recsOfSegs, hmap, hmap]
    apply entsDecode_of_enc hU
    intro p hp hpt
    rcases List.mem_append.1 hp with hp | hp
    · exact entsEnc_segsDs M md true [] Ss p (List.mem_of_mem_drop hp) hpt
    · simp only [pendDs, List.mem_map] at hp
      obtain ⟨e, -, rfl⟩ := hp; exact ⟨e, rfl⟩
  · intro r hr
    have h := noEntLast_drop (noEntLast_segsDs M md true [] Ss) n
    have : (r.typ, r.data) ∈ ((segsDs M md true [] Ss).flatten.drop n).getLast? := by
      rw [← hmap 0#32 (segsDs M md true [] Ss).flatten, ← List.map_drop, List.getLast?_map]
      unfold recsOfSegs at hr
      rw [Option.mem_def] at hr ⊢; rw [hr]; rfl
    exact h _ this
  · intro r hr
    have : (r.typ, r.data) ∈ pendDs M es := by
      rw [← hmap c (pendDs M es)]; exact List.mem_map_of_mem hr
    simp only [pendDs, List.mem_map] at this
    obtain ⟨e, -, he⟩ := this
    exact (congrArg Prod.fst he).symm

end pend

end WalEnc
end EtcdGrove
end Perennial
