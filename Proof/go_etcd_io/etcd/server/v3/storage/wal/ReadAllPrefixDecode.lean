/- A standalone decoder of a closed prefix file starts with CRC zero and reads
the segment's own seed before its ordinary records. -/
module
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllSegment
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairDecode
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllEnd

@[expose] public section
namespace Perennial.EtcdGrove.WalFs
open Fs WalEnc
variable [GooseExts]

/-- The remainder of a prefix probe ends at EOF and contains only snapshot
records which decode to indices strictly below the requested index. -/
structure ProbeBelow (C : WalCodec) (U : WalUnmarshal) (bound : Nat)
    (files : List (List w8)) (off : Nat) (c : w32) : Prop where
  eof : (rdRest C files off c).stop = .eof
  snap : ∀ r ∈ (rdRest C files off c).recs, r.typ = snapshotType →
    ∃ p, U.decSnap r.data = some p ∧ uint.nat p.1 < bound

/-- An accepted CRC record in the scan cannot be a broken link in the CRC
chain because that would end the ordinary reader before EOF. -/
theorem ProbeBelow.next {C U bound files off c files' off' c' r}
    (hp : ProbeBelow C U bound files off c)
    (hd : goDecode C files off c = .ok r files' off' c') :
    (r.typ = snapshotType → ∃ p, U.decSnap r.data = some p ∧ uint.nat p.1 < bound) ∧
      ProbeBelow C U bound files' off' (rdCrc c' r) := by
  have hv : ¬ (r.typ = crcType ∧ crcRecBad c' r) := by
    intro h
    have he := (rdRest_crcRec hd h).2
    rw [hp.eof] at he; cases he
  have hs := rdRest_ok hd hv
  have he := hp.eof
  have hr := hp.snap
  rw [hs] at he hr
  exact ⟨hr r (List.mem_cons_self ..), ⟨he, fun x hx => hr x (List.mem_cons_of_mem _ hx)⟩⟩

/-- Reopening a closed segment as the sole file of a decoder recovers the
original records, including when it was written with a nonzero incoming CRC. -/
theorem readAll_probe_closed {C : WalCodec} (hC : C.Ok) {c : w32} {r : WalRec} {rs : List WalRec}
    (hfit : RecsFit C (r :: rs)) (hch : ChainOk C c (r :: rs)) (ht : r.typ = crcType) :
    let out := rdRest C [recFrames C (r :: rs)] 0 0#32
    out.recs = r :: rs ∧ out.stop = .eof := by
  have h := walDecodeFrom_segFile hC true (z := 0) hfit (chainOk_crcHead hch ht).1 (Or.inl rfl)
  simp only [segFile, List.replicate_zero, List.append_nil] at h
  simp only [rdRest_start, walDecodeFiles, h, and_self]

/-- The contents of one segment strictly before a modern cut. The snapshot in
the first file's header and every snapshot operation obey the same bound. -/
theorem readAll_probe_segment {C : WalCodec} (hC : C.Ok) {M : WalMarshal} {U : WalUnmarshal}
    (hU : U.Ok M) (md : List w8) (first : Bool) (P S : WalHist) (c : w32)
    {I : WalHist} {cut bound : Nat} (hb : walLastIdx (I.take cut) < bound)
    (hpre : ∀ op ∈ S, op ∈ I.take cut)
    (hfit : RecsFit C (chainRecs C c (segHdrDs M md first P ++ S.flatMap (opDs M)))) :
    ProbeBelow C U bound [recFrames C (chainRecs C c (segHdrDs M md first P ++ S.flatMap (opDs M)))] 0 0#32 := by
  let D := segHdrDs M md first P ++ S.flatMap (opDs M)
  have hch : ChainOk C c (chainRecs C c D) := by
    apply chainOk_chainRecs hC
    simpa [D, segsDs] using segsDs_crcOk M md first P [S]
  have hh : ∃ r rs, chainRecs C c D = r :: rs ∧ r.typ = crcType := by
    unfold D segHdrDs
    split <;> simp [hdrDs, cutHdrDs, chainRecs]
  obtain ⟨r, rs, h, ht⟩ := hh
  change RecsFit C (chainRecs C c D) at hfit
  rw [h] at hfit hch
  have hx := readAll_probe_closed hC hfit hch ht
  rw [← h] at hx
  refine ⟨hx.2, ?_⟩
  intro x hm hs
  change x ∈ (rdRest C [recFrames C (chainRecs C c D)] 0 0#32).recs at hm
  rw [hx.1] at hm
  have htd := mem_chainRecs hm
  have hall := dsDec_segsDs hU md first P [S] (x.typ, x.data) (by simpa [segsDs, D] using htd)
  obtain ⟨p, hp⟩ := hall.2.2 hs
  refine ⟨p, hp, ?_⟩
  apply readAll_earlier_probe hU md first P S hb hpre _ hp
  simpa [hs, D] using htd

private theorem segsDs_record_source (M : WalMarshal) (md : List w8) :
    ∀ (first : Bool) (P : WalHist) (Ss : List WalHist) (i : Nat) (D : List (w64 × List w8)), (segsDs M md first P Ss)[i]? = some D →
      ∃ (f : Bool) (pre S : WalHist), Ss[i]? = some S ∧ D = segHdrDs M md f pre ++ S.flatMap (opDs M)
  | _, _, [], _, _, h => by simp [segsDs] at h
  | first, P, S :: Ss, 0, D, h => by
    injection h with h
    exact ⟨first, P, S, rfl, h.symm⟩
  | _, P, S :: Ss, i + 1, D, h => by
    exact segsDs_record_source M md false (P ++ S) Ss i D h

/-- A physical file preceding the filename selected by Open. The selected
name bounds every operation in that file, even when the first live segment
follows a purge. -/
theorem readAll_probe_before_selected {C : WalCodec} (hC : C.Ok) {M : WalMarshal}
    {U : WalUnmarshal} (hU : U.Ok M) {d : WalDur} {lay : WalLay} {ents : Ents}
    (hab : WalAbsD C M d lay ents) {i k : Nat} {g sel : SegG} {bound : Nat}
    (hi : i < k) (hg : lay.segs[i]? = some g) (hsel : lay.segs[k]? = some sel)
    (hname : ∀ sq ix, sel.name = walFileName sq ix → ix < 2 ^ 64 → ix ≤ bound) :
    ProbeBelow C U bound [segImg g] 0 0#32 := by
  obtain ⟨hcp, hlt, hsize⟩ := hab.cuts
  have hk : k < lay.segs.length := (List.getElem?_eq_some_iff.1 hsel).choose
  let Ss := segsOf (histM d) lay.cuts
  let p := lay.first + i
  let q := lay.first + k
  have hpq : p < q := by dsimp [p, q]; omega
  have hq : q ≤ lay.cuts.length := by dsimp [q]; omega
  have hlen : Ss.length = lay.cuts.length + 1 := by simp [Ss, segsOf]
  let rss := segRecs C M d lay.cuts
  have hrs : rss.length = Ss.length := by
    simp [rss, segRecs, Ss, length_chainSegs, length_segsDs]
  have hp : p < rss.length := by omega
  let rs := rss[p]
  have hrs' : rss[p]? = some rs := List.getElem?_eq_getElem hp
  obtain ⟨c, D, hD, he⟩ := chainSegs_getElem? C _ _ _ _ hrs'
  obtain ⟨first, pre, S, hS, hsrc⟩ := segsDs_record_source M d.metadata true [] Ss p D hD
  have hfit : RecsFit C rs := by
    intro r h
    apply hab.fit
    rw [recsOfSegs, ← flatten_chainSegs]
    exact List.mem_flatten.2 ⟨rs, List.mem_of_getElem? hrs', h⟩
  have himg : segImg g = recFrames C rs := by
    rw [segImg, hab.intact i g (by omega) hg, List.map_map]
    change List.map id (segStream C M d lay.cuts p) = _
    rw [List.map_id]
    simp [segStream, List.getD_eq_getElem?_getD, p, rs, rss, List.getElem?_eq_getElem hp]
  rw [himg, he, hsrc]
  rw [he, hsrc] at hfit
  obtain ⟨sq, ix, hn, hix, hb⟩ := hab.nameBound k sel hsel
  have hb' := hb (show 0 < lay.first + k by omega)
  have hix' := hname sq ix hn hix
  apply readAll_probe_segment hC hU _ first pre S c (I := histM d) (cut := segStart lay.cuts q)
    (by dsimp [q]; omega) _ hfit
  have hle : ∀ b ∈ lay.cuts, b ≤ (histM d).length := fun b hb => cut_le_length (hcp b hb)
  have hstart := length_flatten_take_segsOf hlt hle hq
  have hI : histM d = (Ss.take q).flatten ++ (Ss.drop q).flatten := by
    rw [← List.flatten_append, List.take_append_drop]
    exact (segsOf_flatten _ _ (hlt.imp Nat.le_of_lt) hle).symm
  have hpre : (histM d).take (segStart lay.cuts q) = (Ss.take q).flatten := by
    rw [← hstart]
    change (histM d).take (Ss.take q).flatten.length = _
    rw [hI, List.take_left]
  intro op hop
  rw [hpre]
  apply List.mem_flatten.2
  refine ⟨S, List.mem_of_getElem? (i := p) ?_, hop⟩
  rw [List.getElem?_take_of_lt hpq]; exact hS

end Perennial.EtcdGrove.WalFs
