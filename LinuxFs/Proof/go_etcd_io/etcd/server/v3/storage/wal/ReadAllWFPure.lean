/- Lean-first (no Rocq counterpart).

# `ReadAll`'s handle, the pure facts (W3/W5 of `notes/wal-fsext-plan.md`, twenty-sixth session)

What `walOpenWF`'s `walHandleIn` needs of the state `ReadAll` read, pure:

* (b) `walReadAllOk_hs`: the read's hard state is the history's last saved one (`walLastHS`), so the
  handle is quiescent (`WalHS.Done`).
* (c) `readAll_md_some`: a metadata record is among those read (every segment's header has one), so
  the loop's metadata variable is set (`st.md = some _`).
* (e) `walHS_split_read`, `walHS_crc_read`: the encoder made at the tail's end, nothing pending: the
  stream split (`WalHS.Split`) and its CRC the chain's after every record (`WalHS.crc`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllLoop
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalReadAllPost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

section pure
variable [GooseExts]

/-! ## (b) The hard state -/

/-- **The read's hard state is the history's last saved one** (`walReadAt`'s fold from the hard state
before the read position, `walFoldChkFrom_hs`; the snapshots the filter drops carry none). -/
theorem walReadAllOk_hs {I : WalHist} {cut : Nat} {s : w64 × w64} {σ : StorContents}
    (h : walReadAllOk I cut s σ) : σ.hs = walLastHS I := by
  obtain ⟨k, -, -, -, hat⟩ := h
  unfold walReadAt at hat
  rw [walFoldChkFrom_hs hat, walHsStep_filter]
  simp only
  rw [walLastHS_eq, walLastHS_eq, ← List.foldl_append, List.take_append_drop]

/-! ## (c) The metadata record -/

/-- A step keeps the metadata set, and a metadata record's sets it. -/
theorem raStep_mdSome {U : WalUnmarshal} {s : w64 × w64} {st st' : RAState} {td : w64 × List w8}
    (h : raStep U s st td = .ok st') :
    (st.md.isSome = true → st'.md.isSome = true) ∧ (td.1 = metadataType → st'.md.isSome = true) := by
  unfold raStep at h
  by_cases h1 : td.1 = entryType
  · rw [if_pos h1] at h
    refine ⟨fun hs => ?_, fun hm => by rw [hm] at h1; simp [metadataType, entryType] at h1⟩
    split at h
    · cases h
    · split at h
      · cases h
      · cases h; exact hs
  rw [if_neg h1] at h
  by_cases h2 : td.1 = stateType
  · rw [if_pos h2] at h
    refine ⟨fun hs => ?_, fun hm => by rw [hm] at h2; simp [metadataType, stateType] at h2⟩
    split at h
    · cases h
    · cases h; exact hs
  rw [if_neg h2] at h
  by_cases h3 : td.1 = metadataType
  · rw [if_pos h3] at h
    split at h
    · next d hd =>
      split at h
      · cases h; exact ⟨fun hs => hs, fun _ => by rw [hd]; rfl⟩
      · cases h
    · cases h; exact ⟨fun _ => rfl, fun _ => rfl⟩
  rw [if_neg h3] at h
  refine ⟨fun hs => ?_, fun hm => absurd hm h3⟩
  by_cases h4 : td.1 = crcType
  · rw [if_pos h4] at h; cases h; exact hs
  rw [if_neg h4] at h
  by_cases h5 : td.1 = snapshotType
  · rw [if_pos h5] at h
    split at h
    · cases h
    · split at h
      · split at h
        · cases h; exact hs
        · cases h
      · cases h; exact hs
  · rw [if_neg h5] at h; cases h

/-- **The fold over records with a metadata record sets the metadata.** -/
theorem foldlM_raStep_mdSome {U : WalUnmarshal} {s : w64 × w64} :
    ∀ (L : List (w64 × List w8)) (st0 st : RAState), L.foldlM (raStep U s) st0 = .ok st →
      (st0.md.isSome = true ∨ ∃ td ∈ L, td.1 = metadataType) → st.md.isSome = true
  | [], st0, st, h, hm => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rcases hm with hm | ⟨td, htd, -⟩
    · exact hm
    · simp at htd
  | td :: L, st0, st, h, hm => by
    rw [List.foldlM_cons] at h
    generalize hs : raStep U s st0 td = e at h
    cases e with
    | error x => cases h
    | ok st1 =>
      obtain ⟨k1, k2⟩ := raStep_mdSome hs
      refine foldlM_raStep_mdSome L st1 st h ?_
      rcases hm with hm | ⟨td', htd', hm'⟩
      · exact .inl (k1 hm)
      · rcases List.mem_cons.1 htd' with rfl | htd'
        · exact .inl (k2 hm')
        · exact .inr ⟨td', htd', hm'⟩

/-- Every file's header has a metadata record. -/
theorem segsDs_hdr_md (M : WalMarshal) (md : List w8) (first : Bool) (P : WalHist) (S : WalHist)
    (Ss : List WalHist) : (metadataType, md) ∈ (segsDs M md first P (S :: Ss)).flatten := by
  simp only [segsDs, List.flatten_cons, List.mem_append]
  left; left
  unfold segHdrDs
  split
  · simp [hdrDs]
  · simp [cutHdrDs]

/-- **A metadata record is among the records the reader reads from the pinned segments** (over
`walReadFiles_running`: they are the segments' from the first read on, each with its header). -/
theorem readFiles_hasMd {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal}
    {d : WalDur} {lay : WalLay} {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (kk : Nat)
    (hkk : kk < lay.segs.length) :
    ∃ td ∈ (walDecodeFiles C ((lay.segs.drop kk).map segImg) 0#32).recs.map (fun r => (r.typ, r.data)),
      td.1 = metadataType := by
  refine ⟨(metadataType, d.metadata), ?_, rfl⟩
  obtain ⟨-, -, hfl⟩ := hab.cuts
  rw [walReadFiles_running hC hab hex hwr kk hkk]
  generalize hSs : segsOf (histM d) lay.cuts = Ss
  have hSl : Ss.length = lay.cuts.length + 1 := by rw [← hSs]; simp [segsOf]
  generalize hp : lay.first + kk = p
  have hpl : p < Ss.length := by omega
  obtain ⟨S, rest, hdrop⟩ : ∃ S rest, Ss.drop p = S :: rest := by
    cases h : Ss.drop p with
    | nil => rw [List.drop_eq_nil_iff] at h; omega
    | cons S rest => exact ⟨S, rest, rfl⟩
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · subst h0
    rw [List.drop_zero] at hdrop
    subst hdrop
    simp only [List.take_zero]
    have e0 : (recsOfSegs C Mr d.metadata []).length = 0 := rfl
    rw [e0, List.drop_zero, recsOfSegs_map]
    exact segsDs_hdr_md Mr d.metadata true [] S rest
  · have hpre : Ss.take p ≠ [] := by
      intro h
      rw [List.take_eq_nil_iff] at h
      rcases h with h | h
      · omega
      · subst h; simp at hSl
    have := recsOfSegs_drop_map C Mr d.metadata hpre (Ss.drop p)
    rw [List.take_append_drop] at this
    rw [this, hdrop]
    exact segsDs_hdr_md Mr d.metadata false _ S rest

/-- **The loop's metadata variable is set at its end** (`readFiles_hasMd`, the fold `RdLoop.fold`). -/
theorem readAll_md_some {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {U : WalUnmarshal}
    {d : WalDur} {lay : WalLay} {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (kk : Nat)
    (hkk : kk < lay.segs.length) {s : w64 × w64} {st : RAState} {acc : List WalRec}
    (hacc : (walDecodeFiles C ((lay.segs.drop kk).map segImg) 0#32).recs = acc)
    (hf : (acc.map (fun r => (r.typ, r.data))).foldlM (raStep U s) raInit = .ok st) :
    ∃ md, st.md = some md := by
  have := foldlM_raStep_mdSome _ _ _ hf (.inr (hacc ▸ readFiles_hasMd hC hab hex hwr kk hkk))
  exact Option.isSome_iff_exists.1 this

/-! ## (e) The encoder at the tail's end -/

/-- **The stream split of a handle whose encoder starts at the tail's end**, nothing out or pending. -/
theorem walHS_split_read (Mr : WalMarshal) (h : WalHS) (hr : h.rest = 0) (ho : h.out = [])
    (hp : h.pend = []) (hw : h.o0 = (tailStream Mr h.H h.md h.cuts).length) : WalHS.Split Mr h := by
  unfold WalHS.Split WalHS.encRecs
  rw [hr, ho, hp, Nat.sub_zero, List.take_length, ← tailStream_recs, hw, List.take_length]
  simp

/-- **The encoder's CRC of a quiescent handle is the chain's after every record.** -/
theorem walHS_crc_read (Mr : WalMarshal) (h : WalHS) (hr : h.rest = 0) :
    WalHS.crc Mr h = chainEnd walCodec 0#32
      (recsOfSegs walCodec Mr h.md (segsOf (h.H.map WalOpG.toM) h.cuts)) := by
  unfold WalHS.crc allRecs
  rw [hr, Nat.sub_zero, List.take_length]

end pure

end WalFs
end EtcdGrove
end Perennial

end
