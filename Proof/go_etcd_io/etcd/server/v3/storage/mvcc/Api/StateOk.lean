/-
**A store's states are safe to sort** (M4, track B, 2026-11-06; the `Range` contracts' `stateOk`).
Lean-first (no Rocq counterpart). Pure.

Every state of a well formed log (`LogWf'`: revision 0 empty) with fewer than `2 ^ 63` revisions and
at most `2 ^ 62` changes is `stateOk`: at most as many key-values as changes (`stateAfter_length_le`:
a put adds at most one, a delete none), and each positive (`WatchPos.stateAfter_pos`: its revisions
in `[1, |log|)`, its version in `[1, logCh log]`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchPos
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

set_option linter.unusedSectionVars false

variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]

theorem btInsert_length_le' {V : Type} {less : V → V → Prop} [DecidableRel less] (v : V) :
    ∀ l : List V, (btInsert less v l).length ≤ l.length + 1
  | [] => by simp [btInsert]
  | w :: ws => by
    unfold btInsert
    split
    · have := btInsert_length_le' (less := less) v ws; simp; omega
    · split <;> simp

theorem applyChange_length_le (r : w64) (s : List EtcdKv) (c : Change) :
    (applyChange r s c).length ≤ s.length + 1 := by
  cases c with
  | put k v l =>
    simp only [applyChange]
    unfold putKv
    exact btInsert_length_le' _ _
  | del k =>
    simp only [applyChange]
    have := List.length_filter_le (fun x => !decide (x.key = k)) s
    omega

theorem applyChanges_length_le (r : w64) :
    ∀ (cs : List Change) (s : List EtcdKv), (applyChanges r s cs).length ≤ s.length + cs.length := by
  intro cs
  induction cs with
  | nil => intro s; simp [applyChanges]
  | cons c cs ih =>
    intro s
    unfold applyChanges
    rw [List.foldl_cons]
    have h1 := applyChange_length_le r s c
    have h2 := ih (applyChange r s c)
    unfold applyChanges at h2
    simp only [List.length_cons]
    omega

/-- A state has at most as many key-values as its log has changes. -/
theorem stateAfter_length_le (L : Log) : (stateAfter L).length ≤ logCh L := by
  refine posSnocInd (P := fun L => (stateAfter L).length ≤ logCh L) ?_ ?_ L
  · simp [stateAfter]
  · intro L cs ih
    rw [stateAfter_append, logCh_snoc]
    have := applyChanges_length_le (W64 L.length) cs (stateAfter L)
    omega

/-- **Every state of a small well formed log is safe to sort.** -/
theorem stateOk_at (L : Log) (r : Nat) (hwf : LogWf' L) (hlen : L.length < 2 ^ 63)
    (hch : logCh L ≤ 2 ^ 62) : stateOk (stateAt L r) := by
  unfold stateAt
  have hct := logCh_take_le L (r + 1)
  refine ⟨by have := stateAfter_length_le (L.take (r + 1)); omega, fun e he => ?_⟩
  have h0 : (L.take (r + 1)).getD 0 [] = [] := by
    by_cases hL : L = []
    · subst hL; simp
    · have h := hwf.1 hL
      rw [List.getD_eq_getElem?_getD, List.getElem?_take]
      simp [h]
  have hp := stateAfter_pos (L.take (r + 1)) h0
    (by rw [List.length_take]; omega) (by omega) e he
  obtain ⟨h1, -, h3, -, h5, -⟩ := hp
  exact ⟨h1, h3, h5⟩

end api
end mvcc
end EtcdGrove
end Perennial
