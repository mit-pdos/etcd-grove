/- Lean-first (no Rocq counterpart).

# `ReadAll`'s success, pure (W3/W5 of `notes/wal-fsext-plan.md`)

The pure core of `ReadAll`'s success arm in one statement (`readAll_success`): the WAL's static
relation (`WalAbsD`) at the step the proof reads it, its tail idle (`TailExact`, the stream written:
`WalTailIdle`), the segment `kk` the selection opened (named with an index at most the start's), the
start the newest valid pair from the read position; then a successful fold of what the reader reads
from the segments from `kk` on is the restated post (`walReadAllOk`) with the WAL's metadata. The selected segment's name index is bounded (`hnb`, `hsel`:
`walFileName` keeps the index modulo `2^64`, so `WalAbsD.nameBound`'s index, unbounded there, must be
below `2^64` for `walReadTie`'s selection fact to apply; an obligation on the invariant's owner). Over
`walReadFiles_running`, `readAll_ok_pure` and `readPos_le_openPos`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllFiles
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllOk
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllPos

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
    (hcpos : ∀ b ∈ lay.cuts, 0 < b) (kk : Nat) (g : SegG) (hg : lay.segs[kk]? = some g)
    (s : w64 × w64)
    (hsel : ∀ sq ix, g.name = walFileName sq ix → ix < 2 ^ 64 → ix ≤ uint.nat s.1)
    (hnb : ∃ sq ix : Nat, g.name = walFileName sq ix ∧ ix < 2 ^ 64 ∧ (0 < lay.first + kk →
      walLastIdx ((histM d).take (segStart lay.cuts (lay.first + kk))) + 1 ≤ ix))
    (hs : some s = walNewestPair (walValidSnaps (histM d) d.cut)) (stop : WalStop)
    (r : List w8 × HardStateM × List EntryM)
    (hok : readAllFold U s true (walDecodeFiles C ((lay.segs.drop kk).map segImg) 0#32).recs stop =
      .ok r) :
    ∃ σ, walReadAllOk (histM d) d.cut s σ ∧ r = (d.metadata, σ.hs, σ.ents) := by
  have hkk : kk < lay.segs.length := (List.getElem?_eq_some_iff.1 hg).1
  obtain ⟨hcp, hlt, hfl⟩ := hab.cuts
  obtain ⟨hcut, -⟩ := hab.cut
  have hle : ∀ b ∈ lay.cuts, b ≤ (histM d).length := fun b hb => cut_le_length (hcp b hb)
  have hp : lay.first + kk ≤ lay.cuts.length := by omega
  have hk := length_flatten_take_segsOf (I := histM d) hlt hle hp
  rw [walReadFiles_running hC hab hex hwr kk hkk] at hok
  obtain ⟨sq, ix, hnm, hix, hnb⟩ := hnb
  apply readAll_ok_pure hU d.metadata (histM d) lay.cuts (lay.first + kk) d.cut s stop r ⟨hcp, hlt⟩ hp
  · rw [hk, hcut]; exact segStart_mono hlt (by omega) hp
  · intro hp0 hnil
    have h0 := congrArg List.length hnil
    rw [hk, List.length_nil] at h0
    obtain ⟨q, hq⟩ : ∃ q, lay.first + kk = q + 1 := ⟨lay.first + kk - 1, by omega⟩
    have hq' : q < lay.cuts.length := by omega
    rw [hq, segStart_succ hq'] at h0
    have := hcpos _ (List.getElem_mem hq')
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
      obtain ⟨m, hm1, hm2⟩ := hm h0
      rw [hk] at hm1
      exact ⟨hcp _ hmem, hle _ hmem, hnb h0, hsel sq ix hnm hix, m, hm1, hm2⟩
  · exact hs
  · exact hok

end pure

end WalFs
end EtcdGrove
end Perennial
