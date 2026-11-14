/- Lean-first (no Rocq counterpart).

# `ReadAll`'s decode loop, pure (W3/W5 of `notes/wal-fsext-plan.md`, phase 1 of the eighteenth session's plan)

The loop `for err = decoder.Decode(rec); err == nil; err = decoder.Decode(rec) { switch … }`
(S/wal.go:523-596) as an invariant over the decoder's state `(fs, off, c)` (`RdLoop`): what the
reader reads from the start (`R0 = rdRest C fs₀ 0 0#32`, which is `walDecodeFiles`: `rdRest_start`)
is the records handled so far (`acc`) then what it reads from the decoder's state; the fold of `acc`
(`raStep`, `WalEncFold.lean`) is the loop's variables `st`; and the indices `w.enti`/`w.snapi` it
writes are `raIdx`'s fold of `acc`. A record step (`rdLoop_ok`, over `rdRest_ok`: the decoder
accepted `r`, the reader did not reject it as a CRC record) appends it; a stop (`rdLoop_stop`, over
`rdRest_stop`) ends the reader with what was handled.

No arm panics (`MustUnmarshalEntry`, `MustUnmarshalState`, `pbutil.MustUnmarshalMessage`): every record
the reader reads from the WAL's segments is a header's or an operation's (`recsOfSegs_dec`), whose
data the unmarshalling `U` decodes (`RecDec`, from `U.Ok Mr`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllPure
public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncDecoder

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-! ## The records decode -/

/-- **The arms decode the record `r`** (no `Must…` panics on it). -/
def RecDec (U : WalUnmarshal) (r : WalRec) : Prop :=
  (r.typ = entryType → ∃ e, U.decEntry r.data = some e) ∧
  (r.typ = stateType → ∃ h, U.decState r.data = some h) ∧
  (r.typ = snapshotType → ∃ p, U.decSnap r.data = some p)

/-- A record type with a datum the arms decode. -/
def DsDec (U : WalUnmarshal) (td : w64 × List w8) : Prop :=
  (td.1 = entryType → ∃ e, U.decEntry td.2 = some e) ∧
  (td.1 = stateType → ∃ h, U.decState td.2 = some h) ∧
  (td.1 = snapshotType → ∃ p, U.decSnap td.2 = some p)

theorem mem_chainRecs {C : WalCodec} {r : WalRec} :
    ∀ {c : w32} {ds : List (w64 × List w8)}, r ∈ chainRecs C c ds → (r.typ, r.data) ∈ ds
  | _, [] => by simp [chainRecs]
  | c, (t, d) :: ds => by
    intro h
    simp only [chainRecs, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_chainRecs h)

theorem dsDec_opDs {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M) (o : WalOp) :
    ∀ td ∈ opDs M o, DsDec U td := by
  intro td htd
  cases o with
  | save h es =>
    simp only [opDs, List.mem_append, List.mem_map] at htd
    rcases htd with ⟨e, -, rfl⟩ | htd
    · exact ⟨fun _ => ⟨e, hU.entry e⟩, fun h => by simp [entryType, stateType] at h,
        fun h => by simp [entryType, snapshotType] at h⟩
    · split at htd
      · simp at htd
      · simp only [List.mem_singleton] at htd
        subst htd
        exact ⟨fun h => by simp [entryType, stateType] at h, fun _ => ⟨h, hU.state h⟩,
          fun h => by simp [stateType, snapshotType] at h⟩
  | snap m =>
    simp only [opDs, List.mem_singleton] at htd
    subst htd
    exact ⟨fun h => by simp [entryType, snapshotType] at h,
      fun h => by simp [stateType, snapshotType] at h, fun _ => ⟨_, hU.snap m⟩⟩

theorem dsDec_segsDs {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M) (md : List w8) :
    ∀ (first : Bool) (P : WalHist) (Ss : List WalHist),
    ∀ td ∈ (segsDs M md first P Ss).flatten, DsDec U td
  | _, _, [] => by simp [segsDs]
  | first, P, S :: Ss => by
    intro td htd
    simp only [segsDs, List.flatten_cons, List.mem_append] at htd
    rcases htd with (htd | htd) | htd
    · unfold segHdrDs at htd
      split at htd
      · simp only [hdrDs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at htd
        rcases htd with rfl | rfl | rfl
        · exact ⟨fun h => by simp [crcType, entryType] at h, fun h => by simp [crcType, stateType] at h,
            fun h => by simp [crcType, snapshotType] at h⟩
        · exact ⟨fun h => by simp [metadataType, entryType] at h,
            fun h => by simp [metadataType, stateType] at h,
            fun h => by simp [metadataType, snapshotType] at h⟩
        · exact ⟨fun h => by simp [snapshotType, entryType] at h,
            fun h => by simp [snapshotType, stateType] at h, fun _ => ⟨_, hU.snap0⟩⟩
      · simp only [cutHdrDs, List.mem_append, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] at htd
        rcases htd with (rfl | rfl) | htd
        · exact ⟨fun h => by simp [crcType, entryType] at h, fun h => by simp [crcType, stateType] at h,
            fun h => by simp [crcType, snapshotType] at h⟩
        · exact ⟨fun h => by simp [metadataType, entryType] at h,
            fun h => by simp [metadataType, stateType] at h,
            fun h => by simp [metadataType, snapshotType] at h⟩
        · split at htd
          · simp at htd
          · simp only [List.mem_singleton] at htd
            subst htd
            exact ⟨fun h => by simp [entryType, stateType] at h, fun _ => ⟨_, hU.state _⟩,
              fun h => by simp [stateType, snapshotType] at h⟩
    · simp only [List.mem_flatMap] at htd
      obtain ⟨o, -, ho⟩ := htd
      exact dsDec_opDs hU o td ho
    · exact dsDec_segsDs hU md false (P ++ S) Ss td htd

/-- **Every record of the WAL's segments decodes.** -/
theorem recsOfSegs_dec {C : WalCodec} {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M)
    (md : List w8) (Ss : List WalHist) : ∀ r ∈ recsOfSegs C M md Ss, RecDec U r := by
  intro r hr
  exact dsDec_segsDs hU md true [] Ss _ (mem_chainRecs hr)

/-- **What the reader reads from the pinned segments decodes** (over `walReadFiles_running`). -/
theorem readFiles_dec {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {U : WalUnmarshal} (hU : U.Ok Mr)
    {d : WalDur} {lay : WalLay} {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (kk : Nat)
    (hkk : kk < lay.segs.length) :
    ∀ r ∈ (walDecodeFiles C ((lay.segs.drop kk).map segImg) 0#32).recs, RecDec U r := by
  rw [walReadFiles_running hC hab hex hwr kk hkk]
  intro r hr
  exact recsOfSegs_dec hU _ _ r (List.mem_of_mem_drop hr)

/-! ## The indices the loop writes -/

/-- **`w.enti`/`w.snapi` after the record `r`** (S/wal.go:543, :569-571, :583-585): an entry sets
`enti` to its index; a snapshot raises `snapi` to its index, and, of the start's index (`s.1`),
raises `enti` to it. (On a record whose data does not decode, unchanged: no such record is read.) -/
def raIdx (U : WalUnmarshal) (s : w64 × w64) (ix : w64 × w64) (r : WalRec) : w64 × w64 :=
  if r.typ = entryType then
    match U.decEntry r.data with
    | some e => (e.Index', ix.2)
    | none => ix
  else if r.typ = snapshotType then
    match U.decSnap r.data with
    | some p =>
      let sn := if uint.nat ix.2 < uint.nat p.1 then p.1 else ix.2
      let en := if p.1 = s.1 ∧ uint.nat ix.1 < uint.nat p.1 then p.1 else ix.1
      (en, sn)
    | none => ix
  else ix

/-! ## The loop's invariant -/

/-- **The decode loop's pure invariant** (see the file header): from the reader's start `R0`, the
records `acc` handled, the decoder at `(fs, off, c)`, the loop's variables `st` and indices `ix`
(`(w.enti, w.snapi)`). -/
structure RdLoop (C : WalCodec) (U : WalUnmarshal) (s : w64 × w64) (R0 : DecOut) (acc : List WalRec)
    (fs : List (List w8)) (off : Nat) (c : w32) (st : RAState) (ix : w64 × w64) : Prop where
  recs : R0.recs = acc ++ (rdRest C fs off c).recs
  stop : R0.stop = (rdRest C fs off c).stop
  fold : (acc.map (fun r => (r.typ, r.data))).foldlM (raStep U s) raInit = .ok st
  idx : acc.foldl (raIdx U s) (W64 0, W64 0) = ix

/-- The loop's start: a fresh decoder (offset 0, CRC 0), nothing handled. -/
theorem rdLoop_start (C : WalCodec) (U : WalUnmarshal) (s : w64 × w64) (fs : List (List w8)) :
    RdLoop C U s (rdRest C fs 0 0#32) [] fs 0 0#32 raInit (W64 0, W64 0) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **A record step**: the decoder returned `r` (not a CRC record the reader rejects), and the
arm's step is `st'`: `r` is one of the reader's records, and the invariant holds at the decoder's new
state, its CRC updated for a CRC record (`rdCrc`). -/
theorem rdLoop_ok {C : WalCodec} {U : WalUnmarshal} {s : w64 × w64} {R0 : DecOut}
    {acc : List WalRec} {fs fs' : List (List w8)} {off off' : Nat} {c c' : w32} {st st' : RAState}
    {ix : w64 × w64} {r : WalRec} (hL : RdLoop C U s R0 acc fs off c st ix)
    (h : goDecode C fs off c = .ok r fs' off' c') (hok : ¬ (r.typ = crcType ∧ crcRecBad c' r))
    (hst : raStep U s st (r.typ, r.data) = .ok st') :
    r ∈ R0.recs ∧ RdLoop C U s R0 (acc ++ [r]) fs' off' (rdCrc c' r) st' (raIdx U s ix r) := by
  have he := rdRest_ok h hok
  have hrecs : R0.recs = (acc ++ [r]) ++ (rdRest C fs' off' (rdCrc c' r)).recs := by
    rw [hL.recs, he]; simp
  refine ⟨?_, hrecs, ?_, ?_, ?_⟩
  · rw [hrecs]; simp
  · rw [hL.stop, he]
  · rw [List.map_append, List.foldlM_append, hL.fold]
    simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, bind, Except.bind, hst]
    rfl
  · rw [List.foldl_append, hL.idx]; rfl

/-- **A stop**: the decoder returned the stop `s'`: the reader read exactly the records handled, and
stopped with `s'`. -/
theorem rdLoop_stop {C : WalCodec} {U : WalUnmarshal} {s : w64 × w64} {R0 : DecOut}
    {acc : List WalRec} {fs fs' : List (List w8)} {off off' : Nat} {c c' : w32} {st : RAState}
    {ix : w64 × w64} {s' : WalStop} (hL : RdLoop C U s R0 acc fs off c st ix)
    (h : goDecode C fs off c = .stop s' fs' off' c') : R0.recs = acc ∧ R0.stop = s' := by
  obtain ⟨h1, h2, -⟩ := rdRest_stop h
  exact ⟨by rw [hL.recs, h1, List.append_nil], by rw [hL.stop, h2]⟩

/-- **The loop ended at `io.EOF`** (write mode's only accepted stop): the fold of everything the
reader read is the loop's variables, and the success arm's checks are `readAllFold`'s. -/
theorem rdLoop_fold_eof {C : WalCodec} {U : WalUnmarshal} {s : w64 × w64} {R0 : DecOut}
    {acc : List WalRec} {fs : List (List w8)} {off : Nat} {c : w32} {st : RAState}
    {ix : w64 × w64} (hL : RdLoop C U s R0 acc fs off c st ix) (hr : R0.recs = acc)
    (hm : st.matched = true) :
    readAllFold U s true R0.recs .eof = .ok (st.md.getD [], st.hs, st.ents) := by
  unfold readAllFold
  rw [hr, hL.fold]
  simp [bind, Except.bind, hm]

end pure

end WalFs
end EtcdGrove
end Perennial
