/-
Lean-first (no Rocq counterpart). #33 S4: **raft's facts grown by a drain's reports**, the pure
pieces (`Cluster__drain.lean`'s `factsExt`): log matching between two certified logs from raft's
records (`logMatch_of_recs`: `RecsAgree` at `base0`, both logs indexed by their positions), the
`RaftLaws` log-matching conjunct.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open go_etcd_io.raft.v3

section pure
variable [GooseExts]

theorem logIdx_lt {l : List EntryM} (h : AntSim.LogIdx l) {k : Nat} {e : EntryM}
    (hk : l[k]? = some e) : (k : Int) + 1 < 2 ^ 64 := by
  have := h k e hk
  have := uint_Z_lt e.Index'
  omega

/-- The term `plogTermAt` reads at the position `k + 1` of a positionally indexed log is its
`k`-th entry's. -/
theorem plogTermAt_base0_succ {l : List EntryM} (k : Nat) (hk : (k : Int) + 1 < 2 ^ 64) :
    plogTermAt base0 l (pidx base0 (k + 1)) = (fun e : EntryM => e.Term') <$> l[k]? := by
  have hz : uint.Z (pidx base0 (k + 1)) = (k : Int) + 1 := by
    unfold pidx; rw [base0_index]; push_cast
    rw [uint_Z_W64 _ (by omega) (by omega)]; omega
  unfold plogTermAt
  rw [base0_index, hz]
  simp only [show ¬ ((k : Int) + 1 < 0) by omega, show ¬ ((k : Int) + 1 = 0) by omega,
    ↓reduceIte]
  congr 2
  omega

/-- **Log matching from raft's records**: two logs at `base0` whose records agree (`RecsAgree`,
`logRecs_agree`), each indexed by its positions, agree up to any position where their terms do. -/
theorem logMatch_of_recs {l1 l2 : List EntryM} (h1 : AntSim.LogIdx l1) (h2 : AntSim.LogIdx l2)
    (hR : RecsAgree base0 l1 base0 l2) :
    ∀ (k : Nat) (e f : EntryM), l1[k]? = some e → l2[k]? = some f → e.Term' = f.Term' →
      l1.take (k + 1) = l2.take (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro e f he hf ht
    have hlt := logIdx_lt h1 he
    have hi : e.Index' = f.Index' := by
      apply uint_Z_inj.mp; rw [h1 0 e he, h2 0 f hf]
    obtain ⟨hef, -⟩ := hR 0 0 e f he hf (by rw [base0_index]; omega)
      (by rw [base0_index]; omega) ht hi
    subst hef
    rw [List.take_add_one, List.take_add_one, he, hf]
    simp
  | succ k ih =>
    intro e f he hf ht
    have hlt := logIdx_lt h1 he
    have hi : e.Index' = f.Index' := by
      apply uint_Z_inj.mp; rw [h1 _ e he, h2 _ f hf]
    obtain ⟨hef, hpt⟩ := hR (k + 1) (k + 1) e f he hf (by rw [base0_index]; push_cast; omega)
      (by rw [base0_index]; push_cast; omega) ht hi
    subst hef
    have hk1 : k < l1.length := by
      have := (List.getElem?_eq_some_iff.1 he).1; omega
    have hk2 : k < l2.length := by
      have := (List.getElem?_eq_some_iff.1 hf).1; omega
    obtain ⟨e', he'⟩ : ∃ e', l1[k]? = some e' := ⟨_, List.getElem?_eq_getElem hk1⟩
    obtain ⟨f', hf'⟩ : ∃ f', l2[k]? = some f' := ⟨_, List.getElem?_eq_getElem hk2⟩
    rw [plogTermAt_base0_succ k (by omega), plogTermAt_base0_succ k (by omega), he', hf'] at hpt
    simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at hpt
    have ih' := ih e' f' he' hf' hpt
    rw [List.take_add_one, List.take_add_one (l := l2), ih', he, hf]

end pure

end AntHarness
end EtcdGrove
end Perennial
