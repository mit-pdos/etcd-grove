/- Lean-first (no Rocq counterpart).

# `validSnapshotEntries`' fold, pure (W8 of `notes/wal-fsext-plan.md`)

`validSnapshotEntries` (S/wal.go:723-791) decodes every segment from the first and keeps, of the records
it reads, the snapshot records (`MustUnmarshalMessage`, in order: `vseSnaps`) and the last state record
(`MustUnmarshalState`: `vseHs`, from `&raftpb.HardState{}`); then it keeps the snapshots at or below that
state's commit (`vseOut`). On the records of the WAL's segments from the `p`-th on (`walReadFiles_running`,
with `kk = 0` the first named segment `lay.first`), that is `walValidSnaps` of the history from the
segment's start (`vseOut_segs`): `Create`'s zero snapshot record when `p = 0`, then the snapshot records of
the operations; the last state record is the history's last non-empty hard state (a cut's header repeats
the last one, `cutHdrDs`).

The decode loop's invariant (`VsLoop`) is `RdLoop`'s without `ReadAll`'s fold: what the reader reads from
the start is the records handled then what it reads from the decoder's state.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalEncFold
public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncDecoder

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- The snapshot records' (index, term), in order (the arm `case SnapshotType`). -/
def vseSnaps (U : WalUnmarshal) (ds : List (w64 × List w8)) : List (w64 × w64) :=
  ds.filterMap (fun td => if td.1 = snapshotType then U.decSnap td.2 else none)

/-- The arm `case StateType`: the state replaced by the record's. -/
def vseHsStep (U : WalUnmarshal) (h : HardStateM) (td : w64 × List w8) : HardStateM :=
  if td.1 = stateType then (U.decState td.2).getD h else h

/-- The last state record's hard state, from `h`. -/
def vseHs (U : WalUnmarshal) (h : HardStateM) (ds : List (w64 × List w8)) : HardStateM :=
  ds.foldl (vseHsStep U) h

/-- **`validSnapshotEntries`' result** on the records `ds`: the snapshots at or below the last state's
commit. -/
def vseOut (U : WalUnmarshal) (ds : List (w64 × List w8)) : List (w64 × w64) :=
  (vseSnaps U ds).filter (fun p => decide (uint.nat p.1 ≤ uint.nat (vseHs U hsZero ds).Commit'))

/-- The operations' snapshot (index, term) pairs, in order. -/
def snapsOf (H : WalHist) : List (w64 × w64) :=
  H.filterMap (fun o => match o with | .snap m => some (m.Index', m.Term') | .save _ _ => none)

/-- `walLastHS`'s step. -/
def lhsStep (p : HardStateM) (o : WalOp) : HardStateM :=
  match o with | .save h _ => phsNext p h | .snap _ => p

theorem walLastHS_eq (H : WalHist) : walLastHS H = H.foldl lhsStep hsZero := rfl

theorem vseSnaps_append (U : WalUnmarshal) (a b : List (w64 × List w8)) :
    vseSnaps U (a ++ b) = vseSnaps U a ++ vseSnaps U b := by
  simp [vseSnaps, List.filterMap_append]

theorem vseHs_append (U : WalUnmarshal) (h : HardStateM) (a b : List (w64 × List w8)) :
    vseHs U h (a ++ b) = vseHs U (vseHs U h a) b := by
  simp [vseHs, List.foldl_append]

theorem phsNext_self (h : HardStateM) : phsNext h h = h := by
  unfold phsNext; split <;> rfl

theorem phsNext_zero (h : HardStateM) : phsNext hsZero h = h := by
  unfold phsNext
  split
  · rename_i hh
    obtain ⟨t, v, c⟩ := h
    simp only at hh
    obtain ⟨rfl, rfl, rfl⟩ := hh
    rfl
  · rfl

theorem vseSnaps_opDs {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M) (o : WalOp) :
    vseSnaps U (opDs M o) = snapsOf [o] := by
  cases o with
  | save h es =>
    have he : vseSnaps U (es.map (fun e => (entryType, M.encEntry e))) = [] := by
      unfold vseSnaps
      rw [List.filterMap_eq_nil_iff]
      intro td htd
      obtain ⟨e, -, rfl⟩ := List.mem_map.1 htd
      simp [entryType, snapshotType]
    simp only [opDs, vseSnaps_append, he, List.nil_append, snapsOf, List.filterMap_cons,
      List.filterMap_nil]
    split
    · rfl
    · simp [vseSnaps, stateType, snapshotType]
  | snap m =>
    simp [opDs, vseSnaps, snapsOf, hU.snap m]

theorem vseHs_opDs {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M) (h : HardStateM) (o : WalOp) :
    vseHs U h (opDs M o) = lhsStep h o := by
  cases o with
  | save h' es =>
    have he : ∀ h0, vseHs U h0 (es.map (fun e => (entryType, M.encEntry e))) = h0 := by
      intro h0
      unfold vseHs
      induction es generalizing h0 with
      | nil => rfl
      | cons e es ih =>
        simp only [List.map_cons, List.foldl_cons]
        rw [show vseHsStep U h0 (entryType, M.encEntry e) = h0 by simp [vseHsStep, entryType, stateType]]
        exact ih h0
    simp only [opDs, vseHs_append, he, lhsStep]
    by_cases hE : h'.Term' = W64 0 ∧ h'.Vote' = W64 0 ∧ h'.Commit' = W64 0
    · rw [phsNext_empty _ _ hE]
      split
      · rfl
      · rename_i hh; exact absurd hE hh
    · unfold phsNext; rw [if_neg hE]
      split
      · rename_i hh; exact absurd hh hE
      · simp [vseHs, vseHsStep, hU.state]
  | snap m =>
    simp [opDs, vseHs, vseHsStep, lhsStep, snapshotType, stateType]

theorem vseSnaps_ops {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M) :
    ∀ S : WalHist, vseSnaps U (S.flatMap (opDs M)) = snapsOf S
  | [] => rfl
  | o :: S => by
    rw [List.flatMap_cons, vseSnaps_append, vseSnaps_opDs hU, vseSnaps_ops hU S]
    simp [snapsOf, List.filterMap_cons]
    cases o <;> simp

theorem vseHs_ops {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M) :
    ∀ (S : WalHist) (h : HardStateM), vseHs U h (S.flatMap (opDs M)) = S.foldl lhsStep h
  | [], _ => rfl
  | o :: S, h => by
    rw [List.flatMap_cons, vseHs_append, vseHs_opDs hU, vseHs_ops hU S]
    rfl

theorem snapsOf_append (a b : WalHist) : snapsOf (a ++ b) = snapsOf a ++ snapsOf b := by
  simp [snapsOf, List.filterMap_append]

/-- The header records: `Create`'s (the zero snapshot), a cut's (the last state again). -/
theorem vseSnaps_hdr {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M) (md : List w8) (first : Bool)
    (P : WalHist) :
    vseSnaps U (segHdrDs M md first P) = if first then [(W64 0, W64 0)] else [] := by
  cases first
  · simp only [segHdrDs, cutHdrDs, vseSnaps, Bool.false_eq_true, ↓reduceIte]
    split <;> simp [crcType, metadataType, stateType, snapshotType]
  · simp [segHdrDs, hdrDs, vseSnaps, crcType, metadataType, snapshotType, hU.snap0]

theorem vseHs_hdr {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M) (md : List w8) (first : Bool)
    (P : WalHist) (h : HardStateM) :
    vseHs U h (segHdrDs M md first P) = if first then h else phsNext h (walLastHS P) := by
  cases first
  · simp only [segHdrDs, cutHdrDs, Bool.false_eq_true, ↓reduceIte]
    unfold phsNext
    split
    · rename_i hE
      unfold hsEmptyP at hE
      rw [if_pos hE]
      simp [vseHs, vseHsStep, crcType, metadataType, stateType]
    · rename_i hE
      unfold hsEmptyP at hE
      rw [if_neg hE]
      simp [vseHs, vseHsStep, crcType, metadataType, stateType, hU.state]
  · simp [segHdrDs, hdrDs, vseHs, vseHsStep, crcType, metadataType, snapshotType, stateType]

theorem vseSnaps_segsDs {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M) (md : List w8) :
    ∀ (first : Bool) (P : WalHist) (Ss : List WalHist),
    vseSnaps U (segsDs M md first P Ss).flatten =
      (if first ∧ Ss ≠ [] then [(W64 0, W64 0)] else []) ++ snapsOf Ss.flatten
  | _, _, [] => by simp [segsDs, snapsOf, vseSnaps]
  | first, P, S :: Ss => by
    simp only [segsDs, List.flatten_cons, vseSnaps_append, vseSnaps_hdr hU, vseSnaps_ops hU,
      vseSnaps_segsDs hU md false (P ++ S) Ss, snapsOf_append]
    cases first <;> simp

/-- The last state record over the segments, from the state `h` before them (`h` the history's last
state before them: `walLastHS P`; for a cut file any state `phsNext` maps to it). -/
theorem vseHs_segsDs {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M) (md : List w8) :
    ∀ (first : Bool) (P : WalHist) (Ss : List WalHist) (h : HardStateM),
    (first = true → h = walLastHS P) → (first = false → phsNext h (walLastHS P) = walLastHS P) →
    vseHs U h (segsDs M md first P Ss).flatten = if Ss = [] then h else walLastHS (P ++ Ss.flatten)
  | _, _, [], _, _, _ => by simp [segsDs, vseHs]
  | first, P, S :: Ss, h, h1, h2 => by
    simp only [segsDs, List.flatten_cons, vseHs_append, vseHs_hdr hU, vseHs_ops hU]
    have hst : (if first then h else phsNext h (walLastHS P)) = walLastHS P := by
      cases first
      · exact h2 rfl
      · exact h1 rfl
    rw [hst, vseHs_segsDs hU md false (P ++ S) Ss _ (by nofun)
      (fun _ => by
        rw [show S.foldl lhsStep (walLastHS P) = walLastHS (P ++ S) by
          rw [walLastHS_eq, walLastHS_eq, List.foldl_append]]
        exact phsNext_self _)]
    simp only [reduceCtorEq, ↓reduceIte]
    split
    · rename_i hSs
      subst hSs
      simp [walLastHS_eq, List.foldl_append]
    · rw [List.append_assoc]

/-- **`validSnapshotEntries`' result on the WAL's records from the `p`-th segment on** (see the file
header): `walValidSnaps` of the history from the segment's start. -/
theorem vseOut_segs {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M) (md : List w8) (Ss : List WalHist)
    (p : Nat) (hp : p < Ss.length) (hk : 0 < p → (Ss.take p).flatten ≠ []) :
    vseOut U (segsDs M md (decide (p = 0)) (Ss.take p).flatten (Ss.drop p)).flatten =
      walValidSnaps Ss.flatten (Ss.take p).flatten.length := by
  have hne : Ss.drop p ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  have hI : Ss.flatten = (Ss.take p).flatten ++ (Ss.drop p).flatten := by
    rw [← List.flatten_append, List.take_append_drop]
  have hhs : vseHs U hsZero (segsDs M md (decide (p = 0)) (Ss.take p).flatten (Ss.drop p)).flatten =
      walLastHS Ss.flatten := by
    rw [vseHs_segsDs hU md _ _ _ hsZero, if_neg hne, ← hI]
    · intro h0
      have hp0 : p = 0 := of_decide_eq_true h0
      subst hp0; rfl
    · intro _; exact phsNext_zero _
  have hdrop : Ss.flatten.drop (Ss.take p).flatten.length = (Ss.drop p).flatten := by
    rw [hI, List.drop_left]
  unfold vseOut walValidSnaps
  rw [hhs, vseSnaps_segsDs hU md, hdrop, List.filter_append]
  congr 1
  · by_cases hp0 : p = 0
    · subst hp0
      have hSs : Ss ≠ [] := by intro h; subst h; simp at hp
      simp [hSs]
    · have hk' := hk (by omega)
      have hl : (Ss.take p).flatten.length ≠ 0 := fun h => hk' (List.eq_nil_of_length_eq_zero h)
      simp only [hp0, decide_false, Bool.false_eq_true, false_and, ↓reduceIte, if_neg hl,
        List.filter_nil]
  · unfold snapsOf
    rw [List.filter_filterMap]
    congr 1
    funext o
    cases o <;> simp [Option.filter]

/-- **`validSnapshotEntries`' result on what its reader reads from every named segment** (the WAL's
static relation at the pin, its tail idle): `walValidSnaps` of the history from the read position. -/
theorem vseOut_running {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {U : WalUnmarshal} (hU : U.Ok Mr)
    {d : WalDur} {lay : WalLay} {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) :
    vseOut U ((walDecodeFiles C (lay.segs.map segImg) 0#32).recs.map (fun r => (r.typ, r.data))) =
      walValidSnaps (histM d) d.cut := by
  have hne : lay.segs ≠ [] := hab.nonempty
  have hkk : 0 < lay.segs.length := List.length_pos_iff.2 hne
  obtain ⟨hcp, hlt, hfl⟩ := hab.cuts
  obtain ⟨hcut, -⟩ := hab.cut
  have hle : ∀ b ∈ lay.cuts, b ≤ (histM d).length := fun b hb => cut_le_length (hcp b hb)
  have hrun := walReadFiles_running hC hab hex hwr 0 hkk
  rw [List.drop_zero, Nat.add_zero] at hrun
  rw [hrun]
  generalize hSs : segsOf (histM d) lay.cuts = Ss at *
  have hSsl : Ss.length = lay.cuts.length + 1 := by rw [← hSs]; simp [segsOf]
  have hflat : Ss.flatten = histM d := by
    rw [← hSs]; exact segsOf_flatten _ _ (hlt.imp Nat.le_of_lt) hle
  have hp : lay.first < Ss.length := by omega
  have hk := length_flatten_take_segsOf (I := histM d) hlt hle (p := lay.first) (by omega)
  rw [hSs] at hk
  have hk0 : 0 < lay.first → (Ss.take lay.first).flatten ≠ [] := by
    intro hp0 hnil
    have h0 := congrArg List.length hnil
    rw [hk, List.length_nil] at h0
    obtain ⟨q, hq⟩ : ∃ q, lay.first = q + 1 := ⟨lay.first - 1, by omega⟩
    have hq' : q < lay.cuts.length := by omega
    rw [hq, segStart_succ hq'] at h0
    have := hab.cutPos _ (List.getElem_mem hq')
    omega
  have hout := vseOut_segs hU d.metadata Ss lay.first hp hk0
  rw [hflat, hk, ← hcut] at hout
  rw [← hout]
  congr 1
  by_cases hp0 : lay.first = 0
  · rw [hp0]
    simp only [List.take_zero, List.drop_zero, decide_true, List.flatten_nil]
    have h0 : (recsOfSegs C Mr d.metadata []).length = 0 := by simp [recsOfSegs, segsDs, chainRecs]
    rw [h0, List.drop_zero, recsOfSegs_map]
  · have hpre : Ss.take lay.first ≠ [] := by
      intro h; have := congrArg List.length h
      rw [List.length_take, List.length_nil] at this; omega
    have e := recsOfSegs_drop_map C Mr d.metadata hpre (Ss.drop lay.first)
    rw [List.take_append_drop] at e
    rw [e, decide_eq_false hp0]

/-! ## The decode loop's invariant -/

/-- **The decode loop's pure invariant** (`RdLoop` without `ReadAll`'s fold): from the reader's start
`R0`, the records `acc` handled, the decoder at `(fs, off, c)`. -/
structure VsLoop (C : WalCodec) (R0 : DecOut) (acc : List WalRec) (fs : List (List w8)) (off : Nat)
    (c : w32) : Prop where
  recs : R0.recs = acc ++ (rdRest C fs off c).recs
  stop : R0.stop = (rdRest C fs off c).stop

theorem vsLoop_start (C : WalCodec) (fs : List (List w8)) :
    VsLoop C (rdRest C fs 0 0#32) [] fs 0 0#32 := ⟨rfl, rfl⟩

/-- **A record step** (the reader accepts `r`). -/
theorem vsLoop_ok {C : WalCodec} {R0 : DecOut} {acc : List WalRec} {fs fs' : List (List w8)}
    {off off' : Nat} {c c' : w32} {r : WalRec} (hL : VsLoop C R0 acc fs off c)
    (h : goDecode C fs off c = .ok r fs' off' c') (hok : ¬ (r.typ = crcType ∧ crcRecBad c' r)) :
    r ∈ R0.recs ∧ VsLoop C R0 (acc ++ [r]) fs' off' (rdCrc c' r) := by
  have he := rdRest_ok h hok
  have hrecs : R0.recs = (acc ++ [r]) ++ (rdRest C fs' off' (rdCrc c' r)).recs := by
    rw [hL.recs, he]; simp
  refine ⟨?_, hrecs, ?_⟩
  · rw [hrecs]; simp
  · rw [hL.stop, he]

/-- **A stop**: the reader read exactly the records handled. -/
theorem vsLoop_stop {C : WalCodec} {R0 : DecOut} {acc : List WalRec} {fs fs' : List (List w8)}
    {off off' : Nat} {c c' : w32} {s' : WalStop} (hL : VsLoop C R0 acc fs off c)
    (h : goDecode C fs off c = .stop s' fs' off' c') : R0.recs = acc := by
  obtain ⟨h1, -, -⟩ := rdRest_stop h
  rw [hL.recs, h1, List.append_nil]

/-- The records handled are among the reader's. -/
theorem vsLoop_sub {C : WalCodec} {R0 : DecOut} {acc : List WalRec} {fs : List (List w8)}
    {off : Nat} {c : w32} (hL : VsLoop C R0 acc fs off c) : acc <+: R0.recs := by
  rw [hL.recs]; exact List.prefix_append _ _

end pure

end WalFs
end EtcdGrove
end Perennial
