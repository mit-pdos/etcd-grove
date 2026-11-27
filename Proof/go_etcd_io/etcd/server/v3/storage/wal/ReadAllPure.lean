/- Lean-first (no Rocq counterpart).

# `ReadAll`'s success, pure (W3/W5 of `notes/wal-fsext-plan.md`)

The pure core of `ReadAll`'s success arm in one statement (`readAll_success`): the WAL's static
relation (`WalAbsD`) at the step the proof reads it, its tail idle (`TailExact`, the stream written:
`WalTailIdle`), the segment `kk` the selection opened (named with an index at most the start's), the
start the newest valid pair from the read position; then a successful fold, with `pending`, of what the reader reads
from the segments from `kk` on is the restated post (`walReadAllOk`) with the WAL's metadata. The selected
segment's name index is a `uint64` (`WalAbsD.nameBound`: `walFileName` keeps the index modulo `2^64`, so
`walReadTie`'s selection fact `hsel` applies only to an index below `2^64`), and every cut is past the
history's start (`WalAbsD.cutPos`). Over
`walReadFiles_running`, `readAll_ok_pure` and `readPos_le_openPos`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllFiles
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllOk
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllPos
public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncFoldPend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section pure
variable [GooseExts]

theorem segStart_zero (cuts : List Nat) : segStart cuts 0 = 0 := rfl

theorem segStart_succ {cuts : List Nat} {p : Nat} (hp : p < cuts.length) :
    segStart cuts (p + 1) = cuts[p] := by
  unfold segStart
  rw [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_eq_getElem hp,
    Option.getD_some]

theorem segStart_eq {cuts : List Nat} {p : Nat} (hp : p ≤ cuts.length) :
    segStart cuts p = (0 :: cuts)[p]'(by simp; omega) := by
  unfold segStart
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega), Option.getD_some]

/-- Segment starts increase. -/
theorem segStart_le_succ {cuts : List Nat} (h : cuts.Pairwise (· < ·)) {p : Nat}
    (hp : p < cuts.length) : segStart cuts p ≤ segStart cuts (p + 1) := by
  rw [segStart_succ hp]
  cases p with
  | zero => exact Nat.zero_le _
  | succ q =>
    rw [segStart_succ (by omega)]
    exact Nat.le_of_lt (List.pairwise_iff_getElem.1 h q (q + 1) (by omega) hp (by omega))

theorem segStart_mono {cuts : List Nat} (h : cuts.Pairwise (· < ·)) :
    ∀ {i j : Nat}, i ≤ j → j ≤ cuts.length → segStart cuts i ≤ segStart cuts j
  | i, 0, hij, _ => by have : i = 0 := by omega
                       subst this; exact Nat.le_refl _
  | i, j + 1, hij, hj => by
    by_cases e : i = j + 1
    · subst e; exact Nat.le_refl _
    · exact Nat.le_trans (segStart_mono h (by omega) (by omega)) (segStart_le_succ h (by omega))

theorem segsOf_getElem? {I : WalHist} {cuts : List Nat} {p : Nat} (hp : p < cuts.length) :
    (segsOf I cuts)[p]? =
      some ((I.drop (segStart cuts p)).take (segStart cuts (p + 1) - segStart cuts p)) := by
  have h1 : (0 :: cuts)[p]? = some (segStart cuts p) := by
    rw [segStart_eq (Nat.le_of_lt hp)]; exact List.getElem?_eq_getElem _
  have h2 : (cuts ++ [I.length])[p]? = some (segStart cuts (p + 1)) := by
    rw [segStart_succ hp, List.getElem?_append_left hp]; exact List.getElem?_eq_getElem _
  have hz : (List.zip (0 :: cuts) (cuts ++ [I.length]))[p]? = some (segStart cuts p, segStart cuts (p + 1)) :=
    List.getElem?_zip_eq_some.2 ⟨h1, h2⟩
  unfold segsOf
  rw [List.getElem?_map, hz]
  rfl

/-- **The first `p` segments hold the history up to the `p`-th segment's start.** -/
theorem length_flatten_take_segsOf {I : WalHist} {cuts : List Nat} (h : cuts.Pairwise (· < ·))
    (hle : ∀ b ∈ cuts, b ≤ I.length) : ∀ {p : Nat}, p ≤ cuts.length →
    ((segsOf I cuts).take p).flatten.length = segStart cuts p
  | 0, _ => by simp [segStart_zero]
  | p + 1, hp => by
    rw [List.take_succ, segsOf_getElem? (by omega), Option.toList_some, List.flatten_append,
      List.length_append, length_flatten_take_segsOf h hle (by omega)]
    simp only [List.flatten_singleton, List.length_take, List.length_drop]
    have h1 := segStart_le_succ h (p := p) (by omega)
    have h2 : segStart cuts (p + 1) ≤ I.length := by
      rw [segStart_succ (by omega)]; exact hle _ (List.getElem_mem _)
    omega

/-- **`ReadAll`'s success, pure** (see the file header). -/
theorem readAll_success {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {U : WalUnmarshal}
    (hU : U.Ok Mr) {d : WalDur} {lay : WalLay} {ents : Ents} (hab : WalAbsD C Mr d lay ents)
    (hex : TailExact lay) (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length)
    (kk : Nat) (g : SegG) (hg : lay.segs[kk]? = some g)
    (s : w64 × w64)
    (hsel : ∀ sq ix, g.name = walFileName sq ix → ix < 2 ^ 64 → ix ≤ uint.nat s.1)
    (hs : some s = walNewestPair (walValidSnaps (histM d) d.cut)) (stop : WalStop)
    (r : List w8 × HardStateM × List EntryM)
    (hok : readAllFoldP U s true (walDecodeFiles C ((lay.segs.drop kk).map segImg) 0#32).recs stop =
      .ok r) :
    ∃ σ, walReadAllOk (histM d) d.cut s σ ∧ r = (d.metadata, σ.hs, σ.ents) := by
  have hkk : kk < lay.segs.length := (List.getElem?_eq_some_iff.1 hg).1
  obtain ⟨hcp, hlt, hfl⟩ := hab.cuts
  obtain ⟨hcut, -⟩ := hab.cut
  have hle : ∀ b ∈ lay.cuts, b ≤ (histM d).length := fun b hb => cut_le_length (hcp b hb)
  have hp : lay.first + kk ≤ lay.cuts.length := by omega
  have hk := length_flatten_take_segsOf (I := histM d) hlt hle hp
  obtain ⟨es, -, hrec⟩ := walReadFiles_running hC hab hex hwr kk hkk
  rw [hrec, readAllFoldP_wal hU] at hok
  obtain ⟨sq, ix, hnm, hix, hnb⟩ := hab.nameBound kk g hg
  apply readAll_ok_pure hU d.metadata (histM d) lay.cuts (lay.first + kk) d.cut s stop r ⟨hcp, hlt⟩ hp
  · rw [hk, hcut]; exact segStart_mono hlt (by omega) hp
  · intro hp0 hnil
    have h0 := congrArg List.length hnil
    rw [hk, List.length_nil] at h0
    obtain ⟨q, hq⟩ : ∃ q, lay.first + kk = q + 1 := ⟨lay.first + kk - 1, by omega⟩
    have hq' : q < lay.cuts.length := by omega
    rw [hq, segStart_succ hq'] at h0
    have := hab.cutPos _ (List.getElem_mem hq')
    omega
  · intro hm
    rw [hk]
    apply readPos_le_openPos (ix := ix)
    rcases Nat.eq_zero_or_pos (lay.first + kk) with h0 | h0
    · left; rw [h0]; rfl
    · right
      obtain ⟨q, hq⟩ : ∃ q, lay.first + kk = q + 1 := ⟨lay.first + kk - 1, by omega⟩
      have hmem : segStart lay.cuts (lay.first + kk) ∈ lay.cuts := by
        rw [hq, segStart_succ (by omega)]; exact List.getElem_mem _
      obtain ⟨m, al, hm1, hm2⟩ := hm h0
      rw [hk] at hm1
      exact ⟨hcp _ hmem, hle _ hmem, hnb h0, hsel sq ix hnm hix, m, al, hm1, hm2⟩
  · exact hs
  · show normFrom hsZero (normFrom hsZero _) = normFrom hsZero _
    exact normFrom_idem _ _
  · exact hok

/-! ## The read of a history as written -/

theorem walSaveSnap_hs (σ : StorContents) (m : SnapshotMetadataM) : (walSaveSnap σ m).hs = σ.hs := by
  unfold walSaveSnap; split <;> rfl

/-- The fold over a history as written from the running state is the fold over the history. -/
theorem walFoldChkFrom_normFrom (c : Nat) :
    ∀ (D : WalHist) (σ : StorContents),
      walFoldChkFrom σ ((normFrom σ.hs D).filter (walKeep c)) = walFoldChkFrom σ (D.filter (walKeep c))
  | [], σ => rfl
  | .snap m al :: D, σ => by
    simp only [normFrom, normOp, opHS]
    by_cases hk : walKeep c (.snap m al) = true
    · rw [List.filter_cons_of_pos hk, List.filter_cons_of_pos hk]
      simp only [walFoldChkFrom]
      have := walFoldChkFrom_normFrom c D (walSaveSnap σ m)
      rwa [walSaveSnap_hs] at this
    · rw [List.filter_cons_of_neg hk, List.filter_cons_of_neg hk]
      exact walFoldChkFrom_normFrom c D σ
  | .save h es :: D, σ => by
    have hk : ∀ h', walKeep c (.save h' es) = true := fun _ => rfl
    simp only [normFrom, opHS]
    have hn : ∃ h', normOp σ.hs (.save h es) = .save h' es ∧ phsNext σ.hs h' = phsNext σ.hs h := by
      by_cases hc : es ≠ [] ∧ hsEmptyP h
      · refine ⟨σ.hs, by simp [normOp, hc], ?_⟩
        rw [phsNext_self', phsNext_of_hsEmptyP hc.2]
      · exact ⟨h, by simp [normOp, hc], rfl⟩
    obtain ⟨h', hn, hp⟩ := hn
    rw [hn, List.filter_cons_of_pos (hk h'), List.filter_cons_of_pos (hk h)]
    simp only [walFoldChkFrom, hp]
    cases es.foldlM (fun ents e => readEnt σ.b ents e) σ.ents with
    | none => rfl
    | some ents =>
      have := walFoldChkFrom_normFrom c D { σ with hs := phsNext σ.hs h, ents := ents }
      exact congrArg (fun x => (some ents : Option (List EntryM)) >>= fun _ => x) this

theorem walReadAt_normH (I : WalHist) (k : Nat) (s : w64 × w64) :
    walReadAt (normH I) k s = walReadAt I k s := by
  unfold walReadAt
  rw [normH_take, walLastHS_normH, walLastHS_normH, normH_drop]
  exact walFoldChkFrom_normFrom _ (I.drop k) _

/-- **`ReadAll`'s result over the history as written is over the history.** -/
theorem walReadAllOk_normH (I : WalHist) (cut : Nat) (s : w64 × w64) (σ : StorContents) :
    walReadAllOk (normH I) cut s σ ↔ walReadAllOk I cut s σ := by
  unfold walReadAllOk
  simp only [walOpenPos_normH, walValidSnaps_normH, walReadAt_normH]

theorem walReadAllOk_histN (H : List (WalOpG WalEnt)) (cut : Nat) (s : w64 × w64) (σ : StorContents) :
    walReadAllOk (histN H) cut s σ ↔ walReadAllOk (H.map WalOpG.toM) cut s σ :=
  walReadAllOk_normH _ cut s σ

end pure

end WalFs
end EtcdGrove
end Perennial
