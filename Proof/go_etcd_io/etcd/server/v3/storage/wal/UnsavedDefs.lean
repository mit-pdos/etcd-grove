/- Lean-first (no Rocq counterpart).

# What `wal.Unsaved` accepts (pure; P6 of `notes/etcd-dist-d6.md` §10, item 3)

`Unsaved(lg, dir)` (fork `unsaved.go:36`) reads the WAL from its first segment (sequence 0) and returns
`true` when its records hold no state record, no snapshot record above index 0 and no entry record that
another record follows. The proof keeps of that only what the caller needs: the records read hold no state
record and every snapshot record decodes at index 0 (`UnsAcc`). On the records of a WAL read from its first
segment (`walReadFiles_running` at `first = 0`), that makes every operation of the history **blank**
(`walOpBlank`: a `Save` of no entries and the empty hard state, which writes nothing, or a `SaveSnapshot` at
index 0): `unsaved_blank`. A blank history's every prefix is blank (`walBlank_take`): every crash image
(`walImgS`: a prefix of the history) is blank too.

What a blank history reads (`walFresh`, the server's) needs in addition that no snapshot at index 0
carries a nonzero term: raft never saves an empty snapshot (`IsEmptySnap`), a fact of the server's
`SaveSnapshot` calls, not of the WAL; it is the server's obligation (P5/T7).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllFiles
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.VsePure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **A blank operation**: one that writes nothing `Unsaved` rejects. A `Save` of no entries and the
empty hard state (it writes no record), or a `SaveSnapshot` at index 0 (`Create`'s snapshot record is
one too). -/
def walOpBlank : WalOp → Prop
  | .save h es => es = [] ∧ hsEmptyP h
  | .snap m _ => m.Index' = W64 0

/-- **A blank history**: every operation blank (`Unsaved`'s `true`). -/
def walBlank (H : WalHist) : Prop := ∀ o ∈ H, walOpBlank o

/-- **Blank is prefix-closed**: every crash image of a blank history (a prefix) is blank. -/
theorem walBlank_take {H : WalHist} (h : walBlank H) (j : Nat) : walBlank (H.take j) :=
  fun o ho => h o (List.mem_of_mem_take ho)

/-- The history as written is blank only if the history is. -/
theorem walBlank_of_normFrom : ∀ (p : HardStateM) (H : WalHist), walBlank (normFrom p H) → walBlank H
  | _, [], _ => fun _ ho => by cases ho
  | p, o :: H, h => by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · have h0 := h _ (List.mem_cons_self ..)
      cases x with
      | save hs es =>
        by_cases hc : es ≠ [] ∧ hsEmptyP hs
        · have e : normOp p (.save hs es) = .save p es := by simp [normOp, hc]
          rw [e] at h0
          exact absurd h0.1 hc.1
        · have e : normOp p (.save hs es) = .save hs es := by simp [normOp, hc]
          rw [e] at h0
          exact h0
      | snap m al => simpa [normOp] using h0
    · exact walBlank_of_normFrom _ H (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hx

/-- **What `Unsaved`'s loop accepted** of the records `ds` read: no state record, every snapshot record
decoding at index 0. -/
def UnsAcc (U : WalUnmarshal) (ds : List (w64 × List w8)) : Prop :=
  ∀ td ∈ ds, td.1 ≠ stateType ∧ (td.1 = snapshotType → ∀ p, U.decSnap td.2 = some p → p.1 = W64 0)

theorem UnsAcc.nil (U : WalUnmarshal) : UnsAcc U [] := fun _ h => by cases h

theorem UnsAcc.snoc {U : WalUnmarshal} {ds : List (w64 × List w8)} {td : w64 × List w8}
    (h : UnsAcc U ds) (h1 : td.1 ≠ stateType)
    (h2 : td.1 = snapshotType → ∀ p, U.decSnap td.2 = some p → p.1 = W64 0) : UnsAcc U (ds ++ [td]) := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h x hx
  · rw [List.mem_singleton.1 hx]; exact ⟨h1, h2⟩

/-- An operation's records are among its segment's. -/
theorem opDs_mem_segsDs (M : WalMarshal) (md : List w8) :
    ∀ (Ss : List WalHist) (first : Bool) (P : WalHist), ∀ S ∈ Ss, ∀ o ∈ S, ∀ td ∈ opDs M o,
      td ∈ (segsDs M md first P Ss).flatten
  | [], _, _, S, hS, _, _, _, _ => by cases hS
  | S0 :: Ss, first, P, S, hS, o, ho, td, htd => by
    simp only [segsDs, List.flatten_cons]
    rcases List.mem_cons.1 hS with rfl | hS
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨o, ho, htd⟩))
    · exact List.mem_append_right _ (opDs_mem_segsDs M md Ss false (P ++ S0) S hS o ho td htd)

/-- **The accepted records of a WAL's segments are a blank history's.** -/
theorem unsAcc_segs_blank {U : WalUnmarshal} {M : WalMarshal} (hU : U.Ok M) (md : List w8)
    (Ss : List WalHist) (es : List EntryM)
    (h : UnsAcc U ((segsDs M md true [] Ss).flatten ++ pendDs M es)) : walBlank Ss.flatten := by
  intro o ho
  obtain ⟨S, hS, hoS⟩ := List.mem_flatten.1 ho
  have hsub : ∀ td ∈ opDs M o, td ∈ (segsDs M md true [] Ss).flatten ++ pendDs M es :=
    fun td htd => List.mem_append_left _ (opDs_mem_segsDs M md Ss true [] S hS o hoS td htd)
  cases o with
  | save hs es' =>
    by_cases hc : es' = [] ∧ hsEmptyP hs
    · exact hc
    · exfalso
      have hm : (stateType, M.encState hs) ∈ opDs M (.save hs es') := by simp [opDs, hc]
      exact (h _ (hsub _ hm)).1 rfl
  | snap m al =>
    have hm : (snapshotType, M.encSnap m al) ∈ opDs M (.snap m al) := by simp [opDs]
    have := (h _ (hsub _ hm)).2 rfl _ (hU.snap m al)
    exact this

/-- **`Unsaved`'s `true` on what its reader reads from every named segment, read from the first
segment** (`first = 0`; the WAL's static relation at the pin, its tail idle): the history is blank. -/
theorem unsaved_blank {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {U : WalUnmarshal} (hU : U.Ok Mr)
    {d : WalDur} {lay : WalLay} {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (h0 : lay.first = 0)
    (hacc : UnsAcc U ((walDecodeFiles C (lay.segs.map segImg) 0#32).recs.map (fun r => (r.typ, r.data)))) :
    walBlank (d.H.map WalOpG.toM) := by
  have hne : lay.segs ≠ [] := hab.nonempty
  have hkk : 0 < lay.segs.length := List.length_pos_iff.2 hne
  obtain ⟨hcp, hlt, -⟩ := hab.cuts
  have hle : ∀ b ∈ lay.cuts, b ≤ (histM d).length := fun b hb => cut_le_length (hcp b hb)
  obtain ⟨es, -, hrun⟩ := walReadFiles_running hC hab hex hwr 0 hkk
  rw [List.drop_zero, Nat.add_zero, h0, List.take_zero] at hrun
  have hz : (recsOfSegs C Mr d.metadata []).length = 0 := by simp [recsOfSegs, segsDs, chainRecs]
  rw [hz, List.drop_zero] at hrun
  rw [hrun, List.map_append, chainRecs_map, recsOfSegs_map] at hacc
  have hb := unsAcc_segs_blank hU d.metadata _ es hacc
  rw [segsOf_flatten _ _ (hlt.imp Nat.le_of_lt) hle] at hb
  exact walBlank_of_normFrom hsZero _ hb

/-- **A record type the WAL writes**: entry, state, snapshot, metadata or CRC (`Unsaved`'s `default`
arm, an unknown type, is never reached on a WAL's records). -/
def WalTypKnown (t : w64) : Prop :=
  t = entryType ∨ t = stateType ∨ t = snapshotType ∨ t = metadataType ∨ t = crcType

theorem opDs_typ (M : WalMarshal) (o : WalOp) : ∀ td ∈ opDs M o, WalTypKnown td.1 := by
  intro td h
  cases o with
  | save hs es =>
    simp only [opDs, List.mem_append, List.mem_map] at h
    rcases h with ⟨e, -, rfl⟩ | h
    · exact Or.inl rfl
    · split at h
      · cases h
      · rw [List.mem_singleton.1 h]; exact Or.inr (Or.inl rfl)
  | snap m al =>
    simp only [opDs, List.mem_singleton] at h
    subst h; exact Or.inr (Or.inr (Or.inl rfl))

theorem segHdrDs_typ (M : WalMarshal) (md : List w8) (first : Bool) (P : WalHist) :
    ∀ td ∈ segHdrDs M md first P, WalTypKnown td.1 := by
  intro td h
  unfold segHdrDs at h
  split at h
  · simp only [hdrDs, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inl rfl))
  · simp only [cutHdrDs, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with (rfl | rfl) | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · split at h
      · cases h
      · rw [List.mem_singleton.1 h]; exact Or.inr (Or.inl rfl)

theorem segsDs_typ (M : WalMarshal) (md : List w8) :
    ∀ (Ss : List WalHist) (first : Bool) (P : WalHist), ∀ td ∈ (segsDs M md first P Ss).flatten,
      WalTypKnown td.1
  | [], _, _, td, h => by simp [segsDs] at h
  | S :: Ss, first, P, td, h => by
    simp only [segsDs, List.flatten_cons, List.mem_append] at h
    rcases h with (h | h) | h
    · exact segHdrDs_typ M md first P td h
    · obtain ⟨o, -, ho⟩ := List.mem_flatMap.1 h
      exact opDs_typ M o td ho
    · exact segsDs_typ M md Ss false (P ++ S) td h

/-- **Every record the reader reads from every named segment has a known type** (the WAL's static
relation at the pin, its tail idle). -/
theorem running_typ {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal}
    {d : WalDur} {lay : WalLay} {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) :
    ∀ r ∈ (walDecodeFiles C (lay.segs.map segImg) 0#32).recs, WalTypKnown r.typ := by
  intro r hr
  have hkk : 0 < lay.segs.length := List.length_pos_iff.2 hab.nonempty
  obtain ⟨es, -, hrun⟩ := walReadFiles_running hC hab hex hwr 0 hkk
  rw [List.drop_zero] at hrun
  rw [hrun] at hr
  have hm : (r.typ, r.data) ∈ (segsDs Mr d.metadata true [] (segsOf (histM d) lay.cuts)).flatten ++
      pendDs Mr es := by
    rcases List.mem_append.1 hr with h | h
    · apply List.mem_append_left
      rw [← recsOfSegs_map]
      exact List.mem_map_of_mem (List.mem_of_mem_drop h)
    · apply List.mem_append_right
      rw [← chainRecs_map C _ (pendDs Mr es)]
      exact List.mem_map_of_mem h
  rcases List.mem_append.1 hm with h | h
  · exact segsDs_typ Mr d.metadata _ true [] _ h
  · simp only [pendDs, List.mem_map] at h
    obtain ⟨e, -, he⟩ := h
    have : r.typ = entryType := (congrArg Prod.fst he).symm
    rw [this]; exact Or.inl rfl

end pure

end WalFs
end EtcdGrove
end Perennial

end
