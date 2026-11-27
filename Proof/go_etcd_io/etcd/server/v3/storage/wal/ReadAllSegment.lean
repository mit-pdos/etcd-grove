/- The CRC seeds encountered by ReadAll enumerate the selected segment files. -/
module
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllIdx
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.VsePure

@[expose] public section
namespace Perennial.EtcdGrove.WalFs
open Fs WalEnc
variable [GooseExts]

/-- A segment begins with one CRC seed. No operation or remaining header record adds another. -/
private theorem segment_seed (M : WalMarshal) (md : List w8) (first : Bool) (P S : WalHist) :
    ∃ rest, segHdrDs M md first P ++ S.flatMap (opDs M) = (crcType, []) :: rest ∧
      ∀ p ∈ rest, p.1 ≠ crcType := by
  have hbody : ∀ p ∈ S.flatMap (opDs M), p.1 ≠ crcType := by
    intro p hp
    obtain ⟨o, _, ho⟩ := List.mem_flatMap.1 hp
    exact opDs_noCrc M o p ho
  cases first
  · by_cases he : hsEmptyP (walLastHS P)
    · simp [segHdrDs, cutHdrDs, he, metadataType, crcType]
      rintro a b (⟨rfl, -⟩ | ⟨o, ho, hp⟩)
      · decide
      · exact hbody (a, b) (List.mem_flatMap.2 ⟨o, ho, hp⟩)
    · simp [segHdrDs, cutHdrDs, he, metadataType, stateType, crcType]
      rintro a b (⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨o, ho, hp⟩)
      · decide
      · decide
      · exact hbody (a, b) (List.mem_flatMap.2 ⟨o, ho, hp⟩)
  · simp [segHdrDs, hdrDs, metadataType, snapshotType, crcType]
    rintro a b (⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨o, ho, hp⟩)
    · decide
    · decide
    · exact hbody (a, b) (List.mem_flatMap.2 ⟨o, ho, hp⟩)

private theorem segment_seed_count (M : WalMarshal) (md : List w8) (first : Bool) (P S : WalHist) :
    (segHdrDs M md first P ++ S.flatMap (opDs M)).countP (fun p => decide (p.1 = crcType)) = 1 := by
  obtain ⟨rest, he, hn⟩ := segment_seed M md first P S
  have h0 : rest.countP (fun p => decide (p.1 = crcType)) = 0 := by
    rw [List.countP_eq_zero]
    intro p hp
    simp [hn p hp]
  simp [he, List.countP_cons, h0]

/-- At a CRC record, the accumulator is exactly the records of the completed files.
The next lock is at the number of CRC seeds in that accumulator. -/
theorem readAll_crc_position (M : WalMarshal) (md : List w8) :
    ∀ (Ss : List WalHist) (first : Bool) (P : WalHist) (acc : List (w64 × List w8)) (bytes : List w8)
      (suffix : List (w64 × List w8)),
    (segsDs M md first P Ss).flatten = acc ++ (crcType, bytes) :: suffix →
    ∃ before current after, Ss = before ++ current :: after ∧
      acc = (segsDs M md first P before).flatten ∧
      acc.countP (fun p => decide (p.1 = crcType)) = before.length := by
  intro Ss
  induction Ss with
  | nil =>
    intro first P acc bytes suffix h
    simp [segsDs] at h
  | cons S Ss ih =>
    intro first P acc bytes suffix h
    cases acc with
    | nil => exact ⟨[], S, Ss, rfl, rfl, rfl⟩
    | cons seed acc =>
      simp only [segsDs, List.flatten_cons] at h
      obtain ⟨rest, he, hn⟩ := segment_seed M md first P S
      rw [he] at h
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rcases List.append_eq_append_iff.1 h with ⟨more, ha, ht⟩ | ⟨more, hr, ht⟩
      · obtain ⟨B, C, A, hs, hacc, hcount⟩ := ih false (P ++ S) more bytes suffix ht
        refine ⟨S :: B, C, A, by rw [hs]; rfl, ?_, ?_⟩
        · rw [ha, hacc]
          simp [segsDs, he]
        · have hone := segment_seed_count M md first P S
          rw [he] at hone
          rw [ha, ← List.cons_append, List.countP_append, hone, hcount, List.length_cons]
          omega
      · cases more with
        | nil =>
          simp only [List.append_nil] at hr
          obtain ⟨B, C, A, hs, hacc, hcount⟩ := ih false (P ++ S) [] bytes suffix (by simpa using ht.symm)
          refine ⟨S :: B, C, A, by rw [hs]; rfl, ?_, ?_⟩
          · rw [← hr, segsDs, List.flatten_cons, ← hacc, List.append_nil, he]
          · have hone := segment_seed_count M md first P S
            simp only [List.countP_nil] at hcount
            rw [he, hr] at hone
            simpa [← hcount] using hone
        | cons a more =>
          simp only [List.cons_append, List.cons.injEq] at ht
          have ha : a.1 = crcType := by rw [← ht.1]
          exact absurd ha (hn a (by rw [hr]; simp))

private theorem fold_snapi_lt (U : WalUnmarshal) (s : w64 × w64) (bound : Nat) :
    ∀ (ds : List (w64 × List w8)) (ix : w64 × w64), uint.nat ix.2 < bound →
    (∀ p ∈ vseSnaps U ds, uint.nat p.1 < bound) →
    uint.nat (ds.foldl (raIdxT U s) ix).2 < bound := by
  intro ds
  induction ds with
  | nil => intro ix h _; exact h
  | cons td ds ih =>
    intro ix hi hp
    apply ih
    · unfold raIdxT raIdx
      simp only
      split
      · split <;> exact hi
      · split
        · rename_i hs
          cases hdec : U.decSnap td.2 with
          | none => exact hi
          | some p =>
            have h := hp p (by simp [vseSnaps, hs, hdec])
            simp only
            split <;> assumption
        · exact hi
    · intro p hm
      apply hp
      rw [show td :: ds = [td] ++ ds from rfl, vseSnaps_append]
      exact List.mem_append_right _ hm

/-- Every snapshot record in a group of segments before a current-format cut
has an index strictly below the cut's filename. This includes the zero marker. -/
theorem readAll_before_snap_lt {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M)
    (md : List w8) (first : Bool) (P : WalHist) (before : List WalHist)
    {I : WalHist} {cut bound : Nat} (hb : walLastIdx (I.take cut) < bound)
    (hpre : ∀ op ∈ before.flatten, op ∈ I.take cut) {p : w64 × w64}
    (hp : p ∈ vseSnaps U (segsDs M md first P before).flatten) : uint.nat p.1 < bound := by
  rw [vseSnaps_segsDs hU] at hp
  rcases List.mem_append.1 hp with hp | hp
  · split at hp
    · cases List.mem_singleton.1 hp; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hb
    · cases hp
  · obtain ⟨op, hop, hx⟩ := List.mem_filterMap.1 hp
    cases op with
    | save hs es => cases hx
    | snap m al =>
      cases hx
      exact readAll_prefix_snap_lt hb (hpre _ hop)

/-- The prefix probe cannot find the selected start index in an earlier
current-format file. The unmarshal used by the probe is the writer's inverse. -/
theorem readAll_earlier_probe {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M)
    (md : List w8) (first : Bool) (P S : WalHist) {I : WalHist} {cut bound : Nat}
    (hb : walLastIdx (I.take cut) < bound) (hpre : ∀ op ∈ S, op ∈ I.take cut)
    {data : List w8} {p : w64 × w64}
    (hr : (snapshotType, data) ∈ segHdrDs M md first P ++ S.flatMap (opDs M))
    (hu : U.decSnap data = some p) : uint.nat p.1 < bound := by
  apply readAll_before_snap_lt hU md first P [S] hb (by simpa using hpre)
  apply List.mem_filterMap.2
  refine ⟨(snapshotType, data), ?_, by simpa using hu⟩
  simpa [segsDs] using hr

/-- The snapshot high-water mark before a segment is below its current-format
filename index whenever the naming rule bounds the operations before that segment. -/
theorem readAll_segment_snapi_lt {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M)
    (md : List w8) (first : Bool) (P : WalHist) (before : List WalHist) (s : w64 × w64)
    {I : WalHist} {cut bound : Nat} (hb : walLastIdx (I.take cut) < bound)
    (hpre : ∀ op ∈ before.flatten, op ∈ I.take cut) :
    uint.nat ((segsDs M md first P before).flatten.foldl (raIdxT U s) (W64 0, W64 0)).2 < bound := by
  have hpos : 0 < bound := Nat.lt_of_le_of_lt (Nat.zero_le _) hb
  apply fold_snapi_lt
  · exact hpos
  exact fun _ hp => readAll_before_snap_lt hU md first P before hb hpre hp

private theorem segment_count (M : WalMarshal) (md : List w8) (Ss : List WalHist) (first : Bool) (P : WalHist) :
    (segsDs M md first P Ss).flatten.countP (fun p => decide (p.1 = crcType)) = Ss.length := by
  induction Ss generalizing first P with
  | nil => rfl
  | cons S Ss ih =>
    rw [segsDs, List.flatten_cons, List.countP_append, segment_seed_count, ih, List.length_cons, Nat.add_comm]

/-- A CRC record in `X ++ Y` with no CRC record in `Y` is in `X`. -/
theorem split_crc_pend {X Y A B : List (w64 × List w8)} {d : List w8}
    (h : X ++ Y = A ++ (crcType, d) :: B) (hY : ∀ q ∈ Y, q.1 ≠ crcType) :
    ∃ B', X = A ++ (crcType, d) :: B' := by
  rcases List.append_eq_append_iff.1 h with ⟨a', hA, hY'⟩ | ⟨c', hX, hB⟩
  · -- `X` a prefix of `A`: the CRC record in `Y`
    exfalso
    exact hY (crcType, d) (by rw [hY']; simp) rfl
  · rcases c' with _ | ⟨q, c'⟩
    · exfalso
      simp only [List.nil_append] at hB
      exact hY (crcType, d) (by rw [← hB]; simp) rfl
    · simp only [List.cons_append, List.cons.injEq] at hB
      obtain ⟨rfl, -⟩ := hB
      exact ⟨c', hX⟩

private theorem readAll_segment_records {C : WalCodec} (hC : C.Ok) {M : WalMarshal}
    {d : WalDur} {lay : WalLay} {ents : Ents} (hab : WalAbsD C M d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C M d lay.cuts lay.cuts.length).length)
    (kk : Nat) (hkk : kk < lay.segs.length) :
    let Ss := segsOf (histM d) lay.cuts
    let p := lay.first + kk
    ∃ es : List EntryM,
    ((walDecodeFiles C ((lay.segs.drop kk).map segImg) 0#32).recs.map (fun record => (record.typ, record.data))) =
      (segsDs M d.metadata (decide (p = 0)) (Ss.take p).flatten (Ss.drop p)).flatten ++ pendDs M es := by
  dsimp only
  obtain ⟨es, -, hrun⟩ := walReadFiles_running hC hab hex hwr kk hkk
  refine ⟨es, ?_⟩
  rw [hrun, List.map_append, chainRecs_map]
  congr 1
  let Ss := segsOf (histM d) lay.cuts
  let p := lay.first + kk
  change ((recsOfSegs C M d.metadata Ss).drop (recsOfSegs C M d.metadata (Ss.take p)).length).map _ = _
  by_cases hp : p = 0
  · change _ = (segsDs M d.metadata (decide (p = 0)) (Ss.take p).flatten (Ss.drop p)).flatten
    have h0 : (recsOfSegs C M d.metadata []).length = 0 := rfl
    simp only [hp, List.take_zero, List.drop_zero, List.flatten_nil, _root_.decide_true, h0, recsOfSegs_map]
  · have hlen : Ss.length = lay.cuts.length + 1 := by simp [Ss, segsOf]
    have hfl := hab.cuts.2.2
    have hpre : Ss.take p ≠ [] := by
      intro he
      have h := congrArg List.length he
      simp only [List.length_take, List.length_nil] at h
      dsimp [p] at hp h
      omega
    have hx := recsOfSegs_drop_map C M d.metadata hpre (Ss.drop p)
    rw [List.take_append_drop] at hx
    change _ = (segsDs M d.metadata (decide (p = 0)) (Ss.take p).flatten (Ss.drop p)).flatten
    simpa only [decide_eq_false hp] using hx

/-- When the reader rejects a trailing CRC, the accepted records have already
accounted for every lock. The Go branch therefore skips the lock lookup. -/
theorem readAll_crc_count {C : WalCodec} (hC : C.Ok) {M : WalMarshal}
    {d : WalDur} {lay : WalLay} {ents : Ents} (hab : WalAbsD C M d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C M d lay.cuts lay.cuts.length).length)
    (kk : Nat) (hkk : kk < lay.segs.length) :
    (walDecodeFiles C ((lay.segs.drop kk).map segImg) 0#32).recs.countP (fun r => decide (r.typ = crcType)) =
      (lay.segs.drop kk).length := by
  obtain ⟨es, hes⟩ := readAll_segment_records hC hab hex hwr kk hkk
  have h := congrArg (List.countP (fun p : w64 × List w8 => decide (p.1 = crcType))) hes
  have hp0 : (pendDs M es).countP (fun p : w64 × List w8 => decide (p.1 = crcType)) = 0 := by
    rw [List.countP_eq_zero]
    intro q hq
    simp only [pendDs, List.mem_map] at hq
    obtain ⟨e, -, rfl⟩ := hq
    simpa using crcType_ne_entry.symm
  rw [List.countP_append, hp0, Nat.add_zero] at h
  simp only [List.countP_map, Function.comp_def, segment_count, List.length_drop] at h
  have hfl := hab.cuts.2.2
  have hlen : (segsOf (histM d) lay.cuts).length = lay.cuts.length + 1 := by simp [segsOf]
  rw [hlen] at h
  rw [h, List.length_drop]
  omega

/-- At a CRC seed in the decoder, the Go segment counter identifies a real lock
in the selected suffix. For current-format filenames the reader's previous
snapshot high-water mark is either zero or strictly below that file's index. -/
theorem readAll_crc_lock {C : WalCodec} (hC : C.Ok) {M : WalMarshal} {U : WalUnmarshal} (hU : U.Ok M)
    {d : WalDur} {lay : WalLay} {ents : Ents} (hab : WalAbsD C M d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C M d lay.cuts lay.cuts.length).length)
    (kk : Nat) (hkk : kk < lay.segs.length) (acc tail : List WalRec) (r : WalRec) (s : w64 × w64)
    (hrec : (walDecodeFiles C ((lay.segs.drop kk).map segImg) 0#32).recs = acc ++ r :: tail)
    (hcrc : r.typ = crcType) :
    let n := acc.countP (fun record => decide (record.typ = crcType))
    let snapi := (acc.foldl (raIdx U s) (W64 0, W64 0)).2
    ∃ g sq nameIdx, (lay.segs.drop kk)[n]? = some g ∧ g.name = walFileName sq nameIdx ∧
      nameIdx < 2 ^ 64 ∧ (snapi = W64 0 ∨ uint.nat snapi < nameIdx) := by
  dsimp only
  obtain ⟨hcp, hlt, hfl⟩ := hab.cuts
  have hle : ∀ b ∈ lay.cuts, b ≤ (histM d).length := fun b hb => cut_le_length (hcp b hb)
  let Ss := segsOf (histM d) lay.cuts
  let p := lay.first + kk
  have hlen : Ss.length = lay.cuts.length + 1 := by simp [Ss, segsOf]
  have htake : (Ss.take p).length = p := by simp [List.length_take, Nat.min_eq_left (show p ≤ Ss.length by dsimp [p]; omega)]
  let ds := acc.map (fun record => (record.typ, record.data))
  have he : ∃ tl, (segsDs M d.metadata (decide (p = 0)) (Ss.take p).flatten (Ss.drop p)).flatten =
      ds ++ (crcType, r.data) :: tl := by
    obtain ⟨es, hm⟩ := readAll_segment_records hC hab hex hwr kk hkk
    rw [hrec, List.map_append, List.map_cons, hcrc] at hm
    exact split_crc_pend hm.symm (fun q hq => by
      simp only [pendDs, List.mem_map] at hq
      obtain ⟨e, -, rfl⟩ := hq
      exact crcType_ne_entry.symm)
  obtain ⟨tl, he⟩ := he
  obtain ⟨before, S, after, hSs, ha, hn⟩ := readAll_crc_position M d.metadata _ _ _ _ _ _ he
  let n := before.length
  have hn' : acc.countP (fun record => decide (record.typ = crcType)) = n := by simpa [ds, List.countP_map, Function.comp_def] using hn
  have hS : Ss = (Ss.take p ++ before) ++ (S :: after) := by
    rw [List.append_assoc, ← hSs, List.take_append_drop]
  have hlen' := congrArg List.length hS
  simp only [List.length_append, List.length_cons, htake] at hlen'
  have hpos : kk + n < lay.segs.length := by dsimp [n]; dsimp [p] at hlen'; omega
  obtain ⟨g, hg⟩ : ∃ g, lay.segs[kk + n]? = some g := ⟨_, List.getElem?_eq_getElem hpos⟩
  obtain ⟨sq, ix, hname, hix, hbound⟩ := hab.nameBound _ _ hg
  refine ⟨g, sq, ix, ?_, hname, hix, ?_⟩
  · rw [hn', List.getElem?_drop]; exact hg
  by_cases h0 : lay.first + (kk + n) = 0
  · left
    have hn0 : n = 0 := by omega
    have hnil := List.eq_nil_of_length_eq_zero (show before.length = 0 from hn0)
    rw [hnil] at ha
    have hacc : acc = [] := List.map_eq_nil_iff.1 (show ds = [] from ha)
    simp [hacc]
  · right
    have hb := hbound (by omega)
    have hp' : p + n ≤ lay.cuts.length := by dsimp [p]; omega
    have hc := length_flatten_take_segsOf (I := histM d) hlt hle hp'
    have hprelen : (Ss.take p ++ before).length = p + n := by simp [htake, n]
    have hprefix : Ss.take (p + n) = Ss.take p ++ before := by
      calc
        _ = ((Ss.take p ++ before) ++ (S :: after)).take (p + n) := congrArg (List.take (p + n)) hS
        _ = _ := by rw [← hprelen, List.take_left]
    have hhist : histM d = Ss.flatten := (segsOf_flatten _ _ (hlt.imp Nat.le_of_lt) hle).symm
    have hseg : (histM d).take (segStart lay.cuts (p + n)) = (Ss.take p ++ before).flatten := by
      change (Ss.take (p + n)).flatten.length = _ at hc
      rw [hprefix] at hc
      rw [← hc, hhist]
      exact (congrArg (fun xs : List WalHist => xs.flatten.take (Ss.take p ++ before).flatten.length) hS).trans
        (by simp only [List.flatten_append, List.take_left])
    rw [foldl_raIdx_map]
    change uint.nat (ds.foldl (raIdxT U s) _).2 < ix
    rw [ha]
    apply readAll_segment_snapi_lt hU _ _ _ _ _ (I := histM d) (cut := segStart lay.cuts (p + n))
    · dsimp [p]; rw [Nat.add_assoc]; omega
    · intro op hop
      rw [hseg, List.flatten_append]
      exact List.mem_append_right _ hop

/-- Raw Decode can succeed even on a CRC seed which ReadAll will reject. Either
every lock has been visited already, or the seed identifies its own segment. -/
theorem readAll_crc_boundary {C : WalCodec} (hC : C.Ok) {M : WalMarshal} {U : WalUnmarshal} (hU : U.Ok M)
    {d : WalDur} {lay : WalLay} {ents : Ents} (hab : WalAbsD C M d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C M d lay.cuts lay.cuts.length).length)
    (kk : Nat) (hkk : kk < lay.segs.length) {fs fs' : List (List w8)} {off off' : Nat} {c c' : w32}
    {acc : List WalRec} {r : WalRec} {s ix : w64 × w64}
    (hLr : (walDecodeFiles C ((lay.segs.drop kk).map segImg) 0#32).recs = acc ++ (rdRest C fs off c).recs)
    (hLi : acc.foldl (raIdx U s) (W64 0, W64 0) = ix)
    (hd : goDecode C fs off c = .ok r fs' off' c') (hcrc : r.typ = crcType) :
    let n := acc.countP (fun record => decide (record.typ = crcType))
    n = (lay.segs.drop kk).length ∨
    ∃ g sq nameIdx, (lay.segs.drop kk)[n]? = some g ∧ g.name = walFileName sq nameIdx ∧
      nameIdx < 2 ^ 64 ∧ (ix.2 = W64 0 ∨ uint.nat ix.2 < nameIdx) := by
  dsimp only
  have hr := hLr
  by_cases hb : crcRecBad c' r
  · left
    rw [(rdRest_crcRec hd ⟨hcrc, hb⟩).1, List.append_nil] at hr
    rw [← hr]
    exact readAll_crc_count hC hab hex hwr kk hkk
  · right
    rw [rdRest_ok hd (fun h => hb h.2)] at hr
    have h := readAll_crc_lock hC hU hab hex hwr kk hkk acc _ r s hr hcrc
    simpa only [hLi] using h

end Perennial.EtcdGrove.WalFs
