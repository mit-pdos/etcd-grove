/-
# The client's conf-change decisions, by position (2026-10-28, the conf-change decision switch)

The client decides each committed conf entry (`notes/spec-first-study/raft-decisions-spec.md`):
apply a change, or skip it. Its decisions are a ghost map by position (`DecMap`: `some o` the change
`o` applied, `none` the entry skipped), which only grows; every node and every ghost record that
names a configuration holds a lower bound of it (`decLb`, `Protocol/Ghost.lean`), and two lower
bounds of one map agree where both are defined (`DecCompat`), so their union is above both.
Below the ghost files, which name the type; the fold over it is `CfgOverlap.lean`'s `effDec`.
-/
module

public import Proof.go_etcd_io.raft.v3.CCModel

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section decmap
variable [GooseExts]

/-- The client's decisions by position: `some o` the change `o` applied, `none` the entry
skipped. -/
abbrev DecMap := GMap Nat (Option ConfChangeIM)

/-- Two maps that agree where both are defined. -/
def DecCompat (M1 M2 : DecMap) : Prop :=
  ∀ k v1 v2, M1.lookup k = some v1 → M2.lookup k = some v2 → v1 = v2

theorem DecCompat.refl (M : DecMap) : DecCompat M M := by
  intro k v1 v2 h1 h2; rw [h1] at h2; exact Option.some.inj h2

theorem DecCompat.symm {M1 M2 : DecMap} (h : DecCompat M1 M2) : DecCompat M2 M1 :=
  fun k v1 v2 h1 h2 => (h k v2 v1 h2 h1).symm

theorem DecCompat.sub_left (M1 M2 : DecMap) : M1 ⊆ M1 ∪ M2 := by
  intro k v h
  show (M1.lookup k).or (M2.lookup k) = some v
  rw [h]; rfl

theorem DecCompat.sub_right {M1 M2 : DecMap} (hc : DecCompat M1 M2) : M2 ⊆ M1 ∪ M2 := by
  intro k v h
  show (M1.lookup k).or (M2.lookup k) = some v
  cases h1 : M1.lookup k with
  | none => rw [h]; rfl
  | some v1 => rw [hc k v1 v h1 h]; rfl

/-- A map below a compatible one's union, at a larger map. -/
theorem DecCompat.of_sub {M1 M2 M : DecMap} (h1 : M1 ⊆ M) (h2 : M2 ⊆ M) : DecCompat M1 M2 := by
  intro k v1 v2 e1 e2
  have := h1 k v1 e1; rw [h2 k v2 e2] at this; exact (Option.some.inj this).symm

theorem DecMap.sub_refl (M : DecMap) : M ⊆ M := fun _ _ h => h

theorem DecMap.sub_trans {M1 M2 M3 : DecMap} (h1 : M1 ⊆ M2) (h2 : M2 ⊆ M3) : M1 ⊆ M3 :=
  fun k v h => h2 k v (h1 k v h)

theorem DecMap.empty_sub (M : DecMap) : (∅ : DecMap) ⊆ M := by
  intro k v h; simp [GMap.lookup_empty] at h

end decmap

end EtcdGrove
end Perennial
