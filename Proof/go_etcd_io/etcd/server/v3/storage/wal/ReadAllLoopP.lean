/- Lean-first (no Rocq counterpart).

# `ReadAll`'s decode loop with the pending entries (pure; P6 E3, the torn-`Save` fix)

Since the fork's `2bd3048d7` the loop holds the entry records it decodes in `pending` and applies them
(the old entry arm on each, `w.enti` set per entry) when a later record arrives; `lastOff`/`lastCRC`
are the decoder's `LastOffset()`/`LastCRC()` after the last record handled, and `pendOff`/`pendCRC`
their values before the first pending record. `RdLoopP`: the records handled are `accA` (applied: the
loop's variables `st` and the indices `ix` are `RdLoop`'s folds of them; the last of them not an entry
record) then `accP` (pending: entry records decoding to `pending`); the decoder's state is reached from
the start in `|accA ++ accP|` records (`Reach`, `DecReach.lean`) and, with records pending, the state
`(_, pendOff, pendCRC)` in `|accA|`. At the end of a write-mode read (`rdLoopP_eof_wal`) `accA` is the
WAL's records, `accP` the pending run, and `pendOff`/`pendCRC` the last segment's write position and
the chain's CRC (the running WAL's files reach them after the WAL's records, `walReadFiles_running_end`;
the loop is deterministic).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllLoop
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllEnd
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DecReach

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The decode loop's pure invariant with `pending`** (see the file header). -/
structure RdLoopP (C : WalCodec) (U : WalUnmarshal) (s : w64 × w64) (fs0 : List (List w8))
    (accA accP : List WalRec) (pend : List EntryM) (fs : List (List w8)) (off : Nat) (c : w32)
    (st : RAState) (ix : w64 × w64) (pOff : Nat) (pC : w32) : Prop where
  recs : (rdRest C fs0 0 0#32).recs = (accA ++ accP) ++ (rdRest C fs off c).recs
  stop : (rdRest C fs0 0 0#32).stop = (rdRest C fs off c).stop
  endOff : (rdRest C fs0 0 0#32).off = (rdRest C fs off c).off
  endCrc : (rdRest C fs0 0 0#32).crc = (rdRest C fs off c).crc
  fold : (accA.map (fun r => (r.typ, r.data))).foldlM (raStep U s) raInit = .ok st
  idx : accA.foldl (raIdx U s) (W64 0, W64 0) = ix
  lastA : ∀ r ∈ accA.getLast?, r.typ ≠ entryType
  pendT : ∀ r ∈ accP, r.typ = entryType
  pendD : accP.map (fun r => U.decEntry r.data) = pend.map some
  reach : Reach C fs0 0 0#32 fs off c (accA ++ accP).length
  pendAt : accP ≠ [] → ∃ fsP, Reach C fs0 0 0#32 fsP pOff pC accA.length

/-- The loop's start: a fresh decoder, nothing handled or pending. -/
theorem rdLoopP_start (C : WalCodec) (U : WalUnmarshal) (s : w64 × w64) (fs0 : List (List w8))
    (pOff : Nat) (pC : w32) :
    RdLoopP C U s fs0 [] [] [] fs0 0 0#32 raInit (W64 0, W64 0) pOff pC :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => by simp at h, fun _ h => by simp at h, rfl,
    .refl _ _ _, fun h => absurd rfl h⟩

/-- A record the reader does not reject is one of the reader's records. -/
theorem rdLoopP_mem {C : WalCodec} {U : WalUnmarshal} {s : w64 × w64} {fs0 : List (List w8)}
    {accA accP : List WalRec} {pend : List EntryM} {fs fs' : List (List w8)} {off off' : Nat}
    {c c' : w32} {st : RAState} {ix : w64 × w64} {pOff : Nat} {pC : w32} {r : WalRec}
    (hL : RdLoopP C U s fs0 accA accP pend fs off c st ix pOff pC)
    (h : goDecode C fs off c = .ok r fs' off' c') (hok : ¬ (r.typ = crcType ∧ crcRecBad c' r)) :
    r ∈ (rdRest C fs0 0 0#32).recs := by
  rw [hL.recs, rdRest_ok h hok]; simp

/-- **An entry record goes to `pending`**; with nothing pending before, `pendOff`/`pendCRC` become the
decoder's state before it (`lastOff`/`lastCRC`). -/
theorem rdLoopP_ent {C : WalCodec} {U : WalUnmarshal} {s : w64 × w64} {fs0 : List (List w8)}
    {accA accP : List WalRec} {pend : List EntryM} {fs fs' : List (List w8)} {off off' : Nat}
    {c c' : w32} {st : RAState} {ix : w64 × w64} {pOff : Nat} {pC : w32} {r : WalRec} {e : EntryM}
    (hL : RdLoopP C U s fs0 accA accP pend fs off c st ix pOff pC)
    (h : goDecode C fs off c = .ok r fs' off' c') (hT : r.typ = entryType)
    (he : U.decEntry r.data = some e) :
    RdLoopP C U s fs0 accA (accP ++ [r]) (pend ++ [e]) fs' off' c' st ix
      (if pend = [] then off else pOff) (if pend = [] then c else pC) := by
  have hok : ¬ (r.typ = crcType ∧ crcRecBad c' r) := by
    rw [hT]; simp [entryType, crcType]
  have hrc : rdCrc c' r = c' := by simp [rdCrc, hT, entryType, crcType]
  have hre := rdRest_ok h hok
  rw [hrc] at hre
  have hpl : pend = [] ↔ accP = [] := by
    have := congrArg List.length hL.pendD
    simp only [List.length_map] at this
    rw [← List.length_eq_zero_iff, ← this, List.length_eq_zero_iff]
  refine ⟨?_, ?_, ?_, ?_, hL.fold, hL.idx, hL.lastA, ?_, ?_, ?_, ?_⟩
  · rw [hL.recs, hre]; simp
  · rw [hL.stop, hre]
  · rw [hL.endOff, hre]
  · rw [hL.endCrc, hre]
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hL.pendT x hx
    · rw [List.mem_singleton.1 hx]; exact hT
  · rw [List.map_append, List.map_append, hL.pendD]; simp [he]
  · have := reach_snoc hL.reach h hok
    rw [hrc] at this
    simpa [Nat.add_assoc] using this
  · intro _
    by_cases hp : pend = []
    · simp only [hp, ↓reduceIte]
      have hA : accP = [] := hpl.1 hp
      have := hL.reach
      rw [hA, List.append_nil] at this
      exact ⟨fs, this⟩
    · simp only [hp, ↓reduceIte]
      exact hL.pendAt (fun h0 => hp (hpl.2 h0))

/-- **A record that is not an entry's**, after the pending entries are applied (`st1`, `ix1`: the
folds over `accA ++ accP`), and its arm's step `st'`: everything handled is applied. -/
theorem rdLoopP_rec {C : WalCodec} {U : WalUnmarshal} {s : w64 × w64} {fs0 : List (List w8)}
    {accA accP : List WalRec} {pend : List EntryM} {fs fs' : List (List w8)} {off off' : Nat}
    {c c' : w32} {st st1 st' : RAState} {ix ix1 : w64 × w64} {pOff : Nat} {pC : w32} {r : WalRec}
    (hL : RdLoopP C U s fs0 accA accP pend fs off c st ix pOff pC)
    (h : goDecode C fs off c = .ok r fs' off' c') (hT : r.typ ≠ entryType)
    (hok : ¬ (r.typ = crcType ∧ crcRecBad c' r))
    (hf1 : ((accA ++ accP).map (fun r => (r.typ, r.data))).foldlM (raStep U s) raInit = .ok st1)
    (hi1 : (accA ++ accP).foldl (raIdx U s) (W64 0, W64 0) = ix1)
    (hst : raStep U s st1 (r.typ, r.data) = .ok st') (pOff' : Nat) (pC' : w32) :
    RdLoopP C U s fs0 (accA ++ accP ++ [r]) [] [] fs' off' (rdCrc c' r) st' (raIdx U s ix1 r) pOff' pC' := by
  have hre := rdRest_ok h hok
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ h => by simp at h, rfl, ?_, fun h => absurd rfl h⟩
  · rw [hL.recs, hre]; simp
  · rw [hL.stop, hre]
  · rw [hL.endOff, hre]
  · rw [hL.endCrc, hre]
  · rw [List.map_append, List.foldlM_append, hf1]
    simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, bind, Except.bind, hst]
    rfl
  · rw [List.foldl_append, hi1]; rfl
  · intro x hx
    rw [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.mem_def,
      Option.some.injEq] at hx
    rw [← hx]; exact hT
  · have := reach_snoc hL.reach h hok
    simp only [List.length_append, List.length_singleton] at this ⊢
    rwa [Nat.add_assoc] at this

/-- **The flush of `pending`, one entry** (the old entry arm on `pend[i]`): the folds over the handled
records and the first `i` pending ones extend by the `i`-th. -/
theorem rdLoopP_flushStep {U : WalUnmarshal} {s : w64 × w64} {accA accP : List WalRec}
    {pend : List EntryM} {i : Nat} {st : RAState} {ix : w64 × w64}
    (hT : ∀ r ∈ accP, r.typ = entryType) (hD : accP.map (fun r => U.decEntry r.data) = pend.map some)
    (hf : ((accA ++ accP.take i).map (fun r => (r.typ, r.data))).foldlM (raStep U s) raInit = .ok st)
    (hx : (accA ++ accP.take i).foldl (raIdx U s) (W64 0, W64 0) = ix)
    {e : EntryM} (he : pend[i]? = some e) {ents' : List EntryM}
    (hre : readEnt (uint.nat s.1) st.ents e = some ents') :
    ((accA ++ accP.take (i + 1)).map (fun r => (r.typ, r.data))).foldlM (raStep U s) raInit =
        .ok { st with ents := ents' } ∧
      (accA ++ accP.take (i + 1)).foldl (raIdx U s) (W64 0, W64 0) = (e.Index', ix.2) := by
  have hlen : accP.length = pend.length := by
    have := congrArg List.length hD; simpa using this
  have hi : i < accP.length := by
    rw [hlen]; exact (List.getElem?_eq_some_iff.1 he).1
  obtain ⟨r, hr⟩ : ∃ r, accP[i]? = some r := ⟨_, List.getElem?_eq_getElem hi⟩
  have hrT : r.typ = entryType := hT r (List.mem_of_getElem? hr)
  have hrD : U.decEntry r.data = some e := by
    have h1 := congrArg (fun l => l[i]?) hD
    simp only [List.getElem?_map, hr, he, Option.map_some] at h1
    exact Option.some.inj h1
  have htk : accP.take (i + 1) = accP.take i ++ [r] := by
    rw [List.take_succ, hr]; rfl
  rw [htk, ← List.append_assoc]
  constructor
  · rw [List.map_append, List.foldlM_append, hf]
    simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, bind, Except.bind,
      raStep, hrT, if_pos, hrD, hre]
    rfl
  · rw [List.foldl_append, hx]
    simp [raIdx, hrT, hrD]

/-- The flush done: the folds over the handled and all pending records. -/
theorem rdLoopP_flushStart {C : WalCodec} {U : WalUnmarshal} {s : w64 × w64} {fs0 : List (List w8)}
    {accA accP : List WalRec} {pend : List EntryM} {fs : List (List w8)} {off : Nat}
    {c : w32} {st : RAState} {ix : w64 × w64} {pOff : Nat} {pC : w32}
    (hL : RdLoopP C U s fs0 accA accP pend fs off c st ix pOff pC) :
    ((accA ++ accP.take 0).map (fun r => (r.typ, r.data))).foldlM (raStep U s) raInit = .ok st ∧
      (accA ++ accP.take 0).foldl (raIdx U s) (W64 0, W64 0) = ix := by
  simp only [List.take_zero, List.append_nil]; exact ⟨hL.fold, hL.idx⟩

theorem rdLoopP_pend_len {C : WalCodec} {U : WalUnmarshal} {s : w64 × w64} {fs0 : List (List w8)}
    {accA accP : List WalRec} {pend : List EntryM} {fs : List (List w8)} {off : Nat}
    {c : w32} {st : RAState} {ix : w64 × w64} {pOff : Nat} {pC : w32}
    (hL : RdLoopP C U s fs0 accA accP pend fs off c st ix pOff pC) : accP.length = pend.length := by
  have := congrArg List.length hL.pendD; simpa using this

/-- **A stop**: the reader read exactly the records handled, and stopped with `s'`. -/
theorem rdLoopP_stop {C : WalCodec} {U : WalUnmarshal} {s : w64 × w64} {fs0 : List (List w8)}
    {accA accP : List WalRec} {pend : List EntryM} {fs fs' : List (List w8)} {off off' : Nat}
    {c c' : w32} {st : RAState} {ix : w64 × w64} {pOff : Nat} {pC : w32} {s' : WalStop}
    (hL : RdLoopP C U s fs0 accA accP pend fs off c st ix pOff pC)
    (h : goDecode C fs off c = .stop s' fs' off' c') :
    (rdRest C fs0 0 0#32).recs = accA ++ accP ∧ (rdRest C fs0 0 0#32).stop = s' := by
  obtain ⟨h1, h2, -⟩ := rdRest_stop h
  exact ⟨by rw [hL.recs, h1, List.append_nil], by rw [hL.stop, h2]⟩

/-- **A stop's position**: at a stop other than a CRC mismatch, the reader ended at the decoder's
offset and CRC. -/
theorem rdLoopP_stop_end {C : WalCodec} {U : WalUnmarshal} {s : w64 × w64} {fs0 : List (List w8)}
    {accA accP : List WalRec} {pend : List EntryM} {fs fs' : List (List w8)} {off off' : Nat}
    {c c' : w32} {st : RAState} {ix : w64 × w64} {pOff : Nat} {pC : w32} {s' : WalStop}
    (hL : RdLoopP C U s fs0 accA accP pend fs off c st ix pOff pC)
    (h : goDecode C fs off c = .stop s' fs' off' c') (hs : ∀ t, s' ≠ .crcErr t) :
    (rdRest C fs0 0 0#32).off = off' ∧ (rdRest C fs0 0 0#32).crc = c' := by
  obtain ⟨-, -, h3⟩ := rdRest_stop h
  obtain ⟨h4, h5⟩ := h3 hs
  exact ⟨by rw [hL.endOff, h4], by rw [hL.endCrc, h5]⟩

/-- **Splitting at the last non-entry record**: two splits of one list into a part whose last record
is not an entry's and a run of entry records are the same split. -/
theorem split_entRun {A P X Y : List WalRec} (h : A ++ P = X ++ Y)
    (hA : ∀ r ∈ A.getLast?, r.typ ≠ entryType) (hP : ∀ r ∈ P, r.typ = entryType)
    (hX : ∀ r ∈ X.getLast?, r.typ ≠ entryType) (hY : ∀ r ∈ Y, r.typ = entryType) :
    A = X ∧ P = Y := by
  -- the last record of the shorter of `A`, `X` (if any) is in the other's run
  have key : ∀ {A P X Y : List WalRec}, A ++ P = X ++ Y →
      (∀ r ∈ P, r.typ = entryType) → (∀ r ∈ X.getLast?, r.typ ≠ entryType) →
      A.length < X.length → False := by
    intro A P X Y h hP hX hlt
    have hXne : X ≠ [] := by intro h0; rw [h0] at hlt; simp at hlt
    have hi : X.length - 1 < X.length := by omega
    have hget : (A ++ P)[X.length - 1]? = X[X.length - 1]? := by
      rw [h, List.getElem?_append_left hi]
    rw [List.getElem?_append_right (by omega), List.getElem?_eq_getElem hi] at hget
    obtain ⟨hlP, hx⟩ := List.getElem?_eq_some_iff.1 hget
    apply hX (X[X.length - 1]) (by
      rw [List.getLast?_eq_getElem?, Option.mem_def, List.getElem?_eq_getElem hi])
    rw [← hx]
    exact hP _ (List.getElem_mem _)
  have hlen : A.length = X.length := by
    rcases Nat.lt_trichotomy A.length X.length with hl | hl | hl
    · exact (key h hP hX hl).elim
    · exact hl
    · exact (key h.symm hY hA hl).elim
  exact List.append_inj h hlen

/-- The WAL's records from any position end with a record that is not an entry's. -/
theorem recsOfSegs_drop_lastA (C : WalCodec) (M : WalMarshal) (md : List w8) (Ss : List WalHist) (n : Nat) :
    ∀ r ∈ ((recsOfSegs C M md Ss).drop n).getLast?, r.typ ≠ entryType := by
  intro r hr
  have hmap : ∀ c D, (chainRecs C c D).map (fun r => (r.typ, r.data)) = D := chainRecs_map C
  have h := noEntLast_drop (noEntLast_segsDs M md true [] Ss) n
  have : (r.typ, r.data) ∈ ((segsDs M md true [] Ss).flatten.drop n).getLast? := by
    rw [← hmap 0#32 (segsDs M md true [] Ss).flatten, ← List.map_drop, List.getLast?_map]
    unfold recsOfSegs at hr
    rw [Option.mem_def] at hr ⊢; rw [hr]; rfl
  exact h _ this

/-- **The end of a write-mode read of the running WAL** (`io.EOF`): the records applied are the WAL's,
the pending ones the run after them, and, with records pending, `pendOff`/`pendCRC` are the last
segment's write position and the chain's CRC after the WAL's records. -/
theorem rdLoopP_eof_wal {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {U : WalUnmarshal} {s : w64 × w64}
    {d : WalDur} {lay : WalLay} {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (kk : Nat)
    (hkk : kk < lay.segs.length)
    {accA accP : List WalRec} {pend : List EntryM} {fs : List (List w8)} {off : Nat}
    {c : w32} {st : RAState} {ix : w64 × w64} {pOff : Nat} {pC : w32}
    (hL : RdLoopP C U s ((lay.segs.drop kk).map segImg) accA accP pend fs off c st ix pOff pC)
    (hR : (rdRest C ((lay.segs.drop kk).map segImg) 0 0#32).recs = accA ++ accP) :
    ∃ es : List EntryM,
      accA = (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts)).drop
          (recsOfSegs C Mr d.metadata ((segsOf (histM d) lay.cuts).take (lay.first + kk))).length ∧
      accP = chainRecs C (chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts)))
          (pendDs Mr es) ∧
      (es ≠ [] → lay.z0 = (segStream C Mr d lay.cuts lay.cuts.length).length) ∧
      (walDecodeFiles C ((lay.segs.drop kk).map segImg) 0#32).off = lay.wr +
        (recFrames C (chainRecs C (chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts)))
          (pendDs Mr es))).length ∧
      (walDecodeFiles C ((lay.segs.drop kk).map segImg) 0#32).crc =
        crcAfter C (chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts))) (pendDs Mr es) ∧
      (accP ≠ [] → pOff = lay.wr ∧
        pC = chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts))) := by
  obtain ⟨es, hes, hrec, hoff, hcrc, fl, hreach⟩ := walReadFiles_running_end hC hab hex hwr kk hkk
  rw [rdRest_start, hrec] at hR
  have hY : ∀ r ∈ chainRecs C (chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts)))
      (pendDs Mr es), r.typ = entryType := by
    intro r hr
    have := List.mem_map_of_mem (f := fun r : WalRec => (r.typ, r.data)) hr
    rw [chainRecs_map] at this
    simp only [pendDs, List.mem_map] at this
    obtain ⟨e, -, he⟩ := this
    exact (congrArg Prod.fst he).symm
  obtain ⟨hA, hP⟩ := split_entRun hR.symm hL.lastA hL.pendT (recsOfSegs_drop_lastA C Mr _ _ _) hY
  refine ⟨es, hA, hP, hes, hoff, hcrc, fun hne => ?_⟩
  obtain ⟨fsP, hp⟩ := hL.pendAt hne
  rw [hA] at hp
  obtain ⟨-, h1, h2⟩ := reach_det hp hreach
  exact ⟨h1, h2⟩

end pure

end WalFs
end EtcdGrove
end Perennial
