/- Lean-first (no Rocq counterpart).

# The purge's layout step (unit `locks`, session 4; `notes/wal-units/locks.md`)

The `fsExt` counterpart of `walPurge_step`'s state change, on the layout: removing the name of the first
named segment (`lay.first`), when it is not the last, takes the layout to `purgeLay lay` (`first + 1`, the
segments' tail) and the WAL to `walPurgeD d p` (`pur` raised to `p`, the read position `cut` moved to the
next segment's start), given that the removed segment ends at or before `p` (`segStart lay.cuts (first + 1)
≤ p`, what the purger's lock and the handle's locked range give: the purge law, next). `walAbsD_purge`: the
static relation carries over, the directory's `.wal` entries being the remaining segments'.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Abs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- The layout after the first named segment's name is removed. -/
def purgeLay (lay : WalLay) : WalLay := { lay with first := lay.first + 1, segs := lay.segs.tail }

/-- The WAL after a purge up to `p` that removed the first named segment of `lay`: `pur` raised to `p`, the
read position at the next segment's start. -/
def walPurgeD (d : WalDur) (lay : WalLay) (p : Nat) : WalDur :=
  { d with pur := max d.pur p, cut := segStart lay.cuts (lay.first + 1) }

theorem segRecs_purgeD (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (p : Nat)
    (cuts : List Nat) : segRecs C Mr (walPurgeD d lay p) cuts = segRecs C Mr d cuts := rfl

theorem segStream_purgeD (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (p : Nat)
    (cuts : List Nat) (k : Nat) :
    segStream C Mr (walPurgeD d lay p) cuts k = segStream C Mr d cuts k := rfl

/-- **The static relation after a purge of the first named segment** (not the last: `1 < |segs|`), the
segment ending at or before `p`, the directory's `.wal` entries now the other segments'. -/
theorem walAbsD_purge {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents ents' : Ents}
    (h : WalAbsD C Mr d lay ents) (hl : 1 < lay.segs.length)
    (hp : segStart lay.cuts (lay.first + 1) ≤ p)
    (hn : walInos ents' = lay.segs.tail.map (·.ino)) :
    WalAbsD C Mr (walPurgeD d lay p) (purgeLay lay) ents' := by
  obtain ⟨g0, gs, hgs⟩ : ∃ g0 gs, lay.segs = g0 :: gs := by
    cases e : lay.segs with
    | nil => rw [e] at hl; simp at hl
    | cons g0 gs => exact ⟨g0, gs, rfl⟩
  have hgs1 : gs ≠ [] := by rintro rfl; rw [hgs] at hl; simp at hl
  have htail : (purgeLay lay).segs = gs := by simp [purgeLay, hgs]
  refine
    { names := ⟨?_, ?_⟩, cuts := ⟨h.cuts.1, h.cuts.2.1, ?_⟩, nameBound := ?_, cut := ⟨rfl, ?_⟩,
      metas := ?_, intact := ?_, last := ?_, synced := h.synced, lastSynced := h.lastSynced,
      fit := h.fit, tailStop := h.tailStop, nonempty := ?_, cutPos := h.cutPos, seqName := ?_ }
  · rw [hn, htail, hgs]; rfl
  · have := h.names.2; rw [hgs] at this; rw [htail]; exact (List.pairwise_cons.1 this).2
  · have := h.cuts.2.2; rw [hgs] at this; simp only [List.length_cons] at this
    show lay.first + 1 + (purgeLay lay).segs.length = lay.cuts.length + 1
    rw [htail]; omega
  · intro k g hk
    rw [htail] at hk
    have hk' : lay.segs[k + 1]? = some g := by rw [hgs]; exact hk
    obtain ⟨sq, ix, h1, h2, h3⟩ := h.nameBound (k + 1) g hk'
    refine ⟨sq, ix, h1, h2, fun _ => ?_⟩
    have e : (purgeLay lay).first + k = lay.first + (k + 1) := by simp [purgeLay]; omega
    rw [e]; exact h3 (by omega)
  · intro _; exact Nat.le_trans hp (Nat.le_max_right _ _)
  · intro g hg
    rw [htail] at hg
    have hg' : g ∈ lay.segs := by rw [hgs]; exact List.mem_cons_of_mem _ hg
    obtain ⟨a1, a2, a3, a4, a5⟩ := h.metas g hg'
    refine ⟨a1, a2, a3, a4, ?_⟩
    rcases a5 with a5 | a5
    · left; rw [htail]; rw [hgs] at a5
      rw [List.getLast?_cons] at a5
      cases gs with
      | nil => exact absurd rfl hgs1
      | cons g1 gs' => simpa [List.getLast?_cons] using a5
    · exact Or.inr a5
  · intro k g hk hg
    rw [htail] at hk hg
    have hg' : lay.segs[k + 1]? = some g := by rw [hgs]; exact hg
    have hk' : k + 1 + 1 < lay.segs.length := by rw [hgs]; simp; omega
    have := h.intact (k + 1) g hk' hg'
    have e : (purgeLay lay).first + k = lay.first + (k + 1) := by simp [purgeLay]; omega
    rw [this, e]; rfl
  · intro g hg
    rw [htail] at hg
    have hg' : lay.segs.getLast? = some g := by
      rw [hgs]
      cases gs with
      | nil => exact absurd rfl hgs1
      | cons g1 gs' => simpa [List.getLast?_cons] using hg
    exact h.last g hg'
  · rw [htail]; exact hgs1
  · intro k g hk
    rw [htail] at hk
    have hk' : lay.segs[k + 1]? = some g := by rw [hgs]; exact hk
    obtain ⟨ix, hix⟩ := h.seqName (k + 1) g hk'
    refine ⟨ix, ?_⟩
    have e : (purgeLay lay).first + k = lay.first + (k + 1) := by simp [purgeLay]; omega
    rw [e]; exact hix

end pure

end WalFs
end EtcdGrove
end Perennial

end
