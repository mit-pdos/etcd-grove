/-
The writer's `end` (pure lemmas; mvccrand's `TxnEnd.lean`'s model section, at mvccfull's
`commitSt`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.LogModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

theorem commitSt_log (σ : mvcc.api.MvccState) (pend : List Change) :
    (commitSt σ pend).log = commitLog σ.log pend := by
  unfold commitSt MvccState.commitPending MvccState.notify
  by_cases hp : pend = [] <;> simp [hp, commitLog]

theorem commitSt_crev (σ : mvcc.api.MvccState) (pend : List Change) : (commitSt σ pend).crev = σ.crev := rfl

theorem commitSt_pending (σ : mvcc.api.MvccState) (pend : List Change) : (commitSt σ pend).pending = none :=
  rfl

theorem commitSt_notifiedLog_eq (σ : mvcc.api.MvccState) (pend : List Change) :
    (commitSt σ pend).notifiedLog = (commitSt σ pend).log := rfl

theorem commitSt_rev_ge (σ : mvcc.api.MvccState) (pend : List Change) : σ.rev ≤ (commitSt σ pend).rev := by
  unfold MvccState.rev; rw [commitSt_log]
  unfold commitLog; split <;> simp

theorem commitSt_rev_le (σ : mvcc.api.MvccState) (pend : List Change) (h : 1 ≤ σ.log.length) :
    (commitSt σ pend).rev ≤ σ.rev + 1 := by
  unfold MvccState.rev; rw [commitSt_log]
  unfold commitLog; split
  · omega
  · simp; omega

theorem commitSt_len (σ : mvcc.api.MvccState) (pend : List Change) (h : 1 ≤ σ.log.length) :
    (commitSt σ pend).log.length = (commitSt σ pend).rev + 1 := by
  unfold MvccState.rev; rw [commitSt_log]
  unfold commitLog; split
  · omega
  · simp

theorem pendOk_rev' {ks : List GoString} {σ : mvcc.api.MvccState} {Hs : List HRev}
    {pend : List Change} {P : PendM} (hok : pendOk ks σ Hs pend P) :
    P.rev = W64 (Hs.length : Int) := by
  rw [hok.1]; exact pendOf_rev _ _ _

theorem pendOk_chs_nil {ks : List GoString} {σ : mvcc.api.MvccState} {Hs : List HRev}
    {pend : List Change} {P : PendM} (hok : pendOk ks σ Hs pend P) : P.chs = [] ↔ pend = [] := by
  rw [hok.1]; exact pendOf_chs_nil_iff _ _ _

/-- **The revision `end` wants is the committed state's.** -/
theorem viewRev_commit (ks : List GoString) (σ : mvcc.api.MvccState) (Hs : List HRev) (pend : List Change)
    (P : PendM) (hok : pendOk ks σ Hs pend P) (hlen : Hs.length = σ.log.length)
    (h1 : 1 ≤ σ.log.length) (h63 : σ.log.length < 2 ^ 63) :
    viewRev P = W64 ((commitSt σ pend).rev : Int) := by
  have hnil := pendOk_chs_nil hok
  unfold viewRev MvccState.rev
  rw [commitSt_log, pendOk_rev' hok, hlen]
  by_cases hp : pend = []
  · have hc : P.chs = [] := hnil.2 hp
    simp only [hc, ↓reduceIte, commitLog, hp]
    have : ((σ.log.length - 1 : Nat) : Int) = (σ.log.length : Int) - 1 := by omega
    rw [this]; word
  · have hc : P.chs ≠ [] := fun h => hp (hnil.1 h)
    simp only [hc, ↓reduceIte, commitLog, hp, List.length_append, List.length_singleton,
      Nat.add_sub_cancel]

end model

end mvccfull
end EtcdGrove
end Perennial
