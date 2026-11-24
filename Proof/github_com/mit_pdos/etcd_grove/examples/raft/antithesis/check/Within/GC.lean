/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the budget law of `GC` (`State.gc_within`):
it only removes.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem State.gc_within : GCWithin := by
  intro s s' b E hW ho
  unfold State.gc at ho
  obtain ⟨gs, -, ho⟩ := bind_ok ho
  obtain ⟨vs, -, ho⟩ := bind_ok ho
  simp only [pure_ok, Except.ok.injEq] at ho
  subst ho
  have hf : ∀ {α : Type} (l : List α) (p : α → Bool), (l.filter p).length ≤ l.length :=
    fun l p => List.length_filter_le p l
  have hm : ∀ {α : Type} {P : α → Prop} (l : List α) (p : α → Bool), (∀ x ∈ l, P x) → ∀ x ∈ l.filter p, P x :=
    fun l p h x hx => h x (List.mem_filter.1 hx).1
  refine ⟨hW.cfg, hW.i_pos, hW.i_le, hW.currentTerm, hW.voteTerm, hW.commitIndex, hW.lastApplied, hW.confAt,
    hW.confirmed, hW.log, hW.chain, Nat.le_trans (hf _ _) hW.ledLog_len, hm _ _ hW.ledLog, hW.config,
    Nat.le_trans (hf _ _) hW.ledConf_len, hm _ _ hW.ledConf,
    ⟨Nat.le_trans (hf _ _) hW.ledAt.1, hm _ _ hW.ledAt.2⟩, ⟨Nat.le_trans (hf _ _) hW.elAt.1, hm _ _ hW.elAt.2⟩,
    hW.termLen, Nat.le_trans (hf _ _) hW.msgs_len, hm _ _ hW.msgs, Nat.le_trans (hf _ _) hW.votes_len,
    hm _ _ hW.votes, Nat.le_trans (hf _ _) hW.leaders_len, hm _ _ hW.leaders, hW.undo, hW.pending, hW.queue,
    hW.reads, hW.viol⟩

end AntCheck
end EtcdGrove
end Perennial
