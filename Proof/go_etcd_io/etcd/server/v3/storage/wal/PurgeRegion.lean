/- Lean-first (no Rocq counterpart).

# A purge's removal and the region's crashes (unit `locks`, session 6; `notes/wal-units/locks.md`)

Pure. The purge's `os.Remove` of a segment name `bt` logs, on the WAL directory's claim `(j, N, h)`
(coherent), an entry writing only `bt`. A crash that drops it is a crash of the claims before it
(`regionCrashedK_unlog`, `CutCrash.lean`). `regionCrashedK_keptSet`: a crash that keeps it keeps every
earlier entry of the claim (they took effect before the remove's call began), and, with the name `bt` set
back to what it holds now (`treeSetE`), is a crash of the claims before it: so the old crash condition
applies to that tree (`crashTo_dropFirst`, `PurgeCrash.lean`, then drops the segment again). The rename's
`regionCrashedK_kept` is the case of a name holding nothing.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CutCrash
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateCommit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- **A crash that keeps the entry logged at `x`** (writing, among the claim's names, only `bt`) keeps
every earlier entry of the coherent claim, and, with `bt` set back to what the claim holds there now, is
a crash of the claims before it. -/
theorem regionCrashedK_keptSet (cl : List Claim) (n : Nat) (m' : Tree) (K : Nat → Prop) (j : Ino)
    (N : NameSet) (h : NamesH) (x : Nat) (e : LogEntry) (c : Ents) (bt : GoString)
    (hK : RegionCrashedK (replClaim (j, N, h) (j, N, h.log x e c) cl) n m' K) (hx : K x)
    (hcl : (j, N, h) ∈ cl) (hcoh : ClaimCoh h j N) (hs : h.next ≤ e.start)
    (hbt : ∀ b, N.Mem b → e.op.Writes j b → b = bt)
    (hothers : ∀ c' ∈ cl, c' ≠ (j, N, h) → c'.1 = j → ¬ c'.2.1.Mem bt) :
    (∀ xe ∈ h.ents, K xe.1) ∧ RegionCrashedK cl n (treeSetE m' j bt (h.cur !! bt)) K := by
  classical
  have hold : ∀ xe ∈ h.ents, K xe.1 := by
    intro xe hxe
    have hc1 : (j, N, h.log x e c) ∈ replClaim (j, N, h) (j, N, h.log x e c) cl := by
      have := mem_replClaim (c0 := (j, N, h)) (c1 := (j, N, h.log x e c)) hcl
      simpa using this
    exact hK.1 _ hc1 _ hc1 x e c xe.1 xe.2.1 xe.2.2 (by simp [NamesH.log])
      (by simp [NamesH.log, hxe]) hx (Nat.lt_of_lt_of_le (hcoh.1 xe hxe) hs)
  refine ⟨hold, ?_⟩
  let f : Claim → Claim := fun c' => if c' = (j, N, h) then (j, N, h.log x e c) else c'
  have hfe : ∀ c' y, y ∈ c'.2.2.ents → y ∈ (f c').2.2.ents := fun c' y hy => by
    simp only [f]; split
    · rename_i hc; subst hc; simp [NamesH.log, hy]
    · exact hy
  obtain ⟨h1, h2, h3⟩ := hK
  refine ⟨fun c1 hc1 c2 hc2 x' e' E y e'' E' hx' hy hKx hlt => ?_, fun c1 hc1 y e' E hy hlt => ?_,
    fun c1 hc1 b hb => ?_⟩
  · exact h1 (f c1) (mem_replClaim hc1) (f c2) (mem_replClaim hc2) x' e' E y e'' E'
      (hfe c1 _ hx') (hfe c2 _ hy) hKx hlt
  · exact h2 (f c1) (mem_replClaim hc1) y e' E (hfe c1 _ hy) hlt
  · have h3' := h3 (f c1) (mem_replClaim hc1)
    rw [treeSetE_entry]
    by_cases hc : c1 = (j, N, h)
    · subst hc
      simp only [f, ite_true] at h3'
      by_cases hb' : b = bt
      · subst hb'
        simp only [and_self, ite_true]
        rw [hcoh.2 K hold b hb]
      · simp only [hb', and_false, ite_false]
        rw [h3' b hb]
        exact valAfter_log_notWrites _ _ _ _ _ _ _ (fun hw => hb' (hbt b hb hw))
    · simp only [f, hc, ite_false] at h3'
      have : ¬ (c1.1 = j ∧ b = bt) := fun ⟨e1, e2⟩ => hothers c1 hc1 hc e1 (e2 ▸ hb)
      simp only [this, ite_false]
      exact h3' b hb

end pure

end WalFs
end EtcdGrove
end Perennial

end
