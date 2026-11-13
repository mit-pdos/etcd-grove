/-
The writer's step of the log model (pure): a member's store state after an operation whose
revision's model is `opPend` is the committed state of the transaction that made it
(`σOf_succ_commit`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.LogLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.EndLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

theorem foldl_step_chs_map (cs : List Change) : ∀ P : PendM,
    (cs.foldl PendM.step P).chs.map toChange = P.chs.map toChange ++ cs := by
  induction cs with
  | nil => intro P; simp
  | cons c cs ih =>
    intro P
    rw [List.foldl_cons, ih]
    cases c with
    | put k v l =>
      simp only [PendM.step, PendM.put, List.map_append, List.map_cons, List.map_nil,
        toChange_put, List.append_assoc, List.cons_append, List.nil_append]
    | del k =>
      simp only [PendM.step, PendM.delOne, List.map_append, List.map_cons, List.map_nil,
        toChange_delChange, List.append_assoc, List.cons_append, List.nil_append]

/-- **mvcc's changes of a revision are the tester's.** -/
theorem pendOf_chs_map (M : GMap GoString kvRec) (r : w64) (cs : List Change) :
    (pendOf M r cs).chs.map toChange = cs := by
  unfold pendOf; rw [foldl_step_chs_map]; simp

theorem logOfHist_histAfter (Hs : List HRev) (P : PendM) :
    logOfHist (histAfter Hs P) = commitLog (logOfHist Hs) (P.chs.map toChange) := by
  unfold histAfter commitLog
  by_cases hc : P.chs = []
  · simp [hc]
  · have : P.chs.map toChange ≠ [] := by simpa using hc
    simp only [hc, ↓reduceIte, this, logOfHist_append]

/-- **The member's state after the operation is the committed transaction's** (an operation that
compacts nothing: `opStep`'s compaction revision unchanged), its history the history with the
revision's model appended. -/
theorem σOf_succ_commit (ks : List GoString) (ops : List OpM) (n : Nat) (o : OpM)
    (ho : ops[n]? = some o) (pend : List Change)
    (hok : pendOk ks (σOf ks ops n) (histAt ks ops n) pend (opPend ks (runM ks ops n) o))
    (hcr : cmpAfter ks ops (n + 1) = cmpAfter ks ops n) :
    σOf ks ops (n + 1) = commitSt (σOf ks ops n) pend ∧
      histAt ks ops (n + 1) = histAfter (histAt ks ops n) (opPend ks (runM ks ops n) o) := by
  have hs : runM ks ops (n + 1) = opStep ks (runM ks ops n) o := runM_succ ks ops n o ho
  have hh : histAt ks ops (n + 1) = histAfter (histAt ks ops n) (opPend ks (runM ks ops n) o) := by
    unfold histAt; rw [hs]; rfl
  refine ⟨?_, hh⟩
  have hchs : (opPend ks (runM ks ops n) o).chs.map toChange = pend := by
    rw [hok.1]; exact pendOf_chs_map _ _ _
  have hlog : (commitSt (σOf ks ops n) pend).log = (σOf ks ops (n + 1)).log := by
    rw [commitSt_log]
    show commitLog (logOfHist (histAt ks ops n)) pend = logOfHist (histAt ks ops (n + 1))
    rw [hh, logOfHist_histAfter, hchs]
  have hc : (commitSt (σOf ks ops n) pend).crev = (σOf ks ops (n + 1)).crev := by
    rw [commitSt_crev]; show cmpAfter ks ops n = cmpAfter ks ops (n + 1); rw [hcr]
  have hp : (commitSt (σOf ks ops n) pend).pending = (σOf ks ops (n + 1)).pending := rfl
  cases h1 : commitSt (σOf ks ops n) pend
  cases h2 : σOf ks ops (n + 1)
  rw [h1, h2] at hlog hc hp
  simp only at hlog hc hp
  rw [hlog, hc, hp]

end model

end mvccfull
end EtcdGrove
end Perennial
