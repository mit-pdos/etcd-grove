/-
**The file's partial last page after a failed write** (U10o, for `Tx.Commit_err`'s rollback after
`tx.write` fails): `wdbOK`'s partial-page clause for the writer side with every written slot
(the dirty pages' and the tail's, `bufSlots ++ cmTail`) taking the write's bytes, without
`Tx.write_ext.spec`'s success-only alignment. A slot across the new end is either across the old
one (the file kept its size: `wdbOK`'s clause) or, the file having grown, inside the mapping's whole
slots (`Tx.write_ext.spec`'s bound `max size (4096 * (l / 4096))`), past the old end, so a written
slot (`cmTail`), whose bytes the spec bounds.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.TailWrite
public import Proof.go_etcd_io.bbolt.Inv.WdbFlag

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

theorem cm_write_part_err' (fr : Bool) (w : WDb) (m' : OsMeta) (SB : List Nat) (l : Nat)
    (wb' : Nat → List w8) (hok : wdbOK' fr w)
    (hW : ∀ s, s < l / 4096 → w.m.size < 4096 * (s + 1) → s ∈ w.W)
    (hsz1 : w.m.size ≤ m'.size) (hsz : m'.size ≤ max w.m.size (4096 * (l / 4096)))
    (hw : ∀ s ∈ SB ++ cmTail w SB l, 4096 * s < m'.size → m'.size < 4096 * (s + 1) →
      m'.size - 4096 * s ≤ (wb' s).length) :
    ∀ s, 4096 * s < m'.size → m'.size < 4096 * (s + 1) →
      m'.size - 4096 * s ≤ (wbUpd (SB ++ cmTail w SB l) wb' w.wb s).length := by
  intro s h1 h2
  unfold wbUpd
  by_cases hs : s ∈ SB ++ cmTail w SB l
  · rw [if_pos hs]; exact hw s hs h1 h2
  · rw [if_neg hs]
    by_cases e : m'.size = w.m.size
    · have hold := (wdbOK'_noFl fr w hok).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [e] at h1 h2 ⊢
      exact hold s h1 h2
    · exfalso
      have hgt : w.m.size < m'.size := Nat.lt_of_le_of_ne hsz1 (Ne.symm e)
      have hle : m'.size ≤ 4096 * (l / 4096) := by omega
      have hsl : s < l / 4096 := by omega
      have hwg : w.m.size < 4096 * (s + 1) := by omega
      apply hs
      by_cases hSB : s ∈ SB
      · exact List.mem_append_left _ hSB
      · exact List.mem_append_right _ ((mem_cmTail w SB l s).2 ⟨hsl, hW s hsl hwg, hwg, hSB⟩)

end pure

end bbolt
end EtcdGrove
end Perennial
