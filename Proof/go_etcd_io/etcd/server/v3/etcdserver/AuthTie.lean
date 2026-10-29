/-
**The tie of the auth store's history to the log** (H5, 2026-10-29; `notes/decisions.md`, "H5: the
auth history's cap"): the pure facts the server's tie (`authHistTie`, `KVApplyOn.lean`) rests on.

- `authOrd`: a state's order, twice its revision plus its flag. Every admin step the model
  records raises it (`adminNext_ord`): the steps bump the revision, but for `AuthEnable`, which
  sets the flag from `false`.
- `srvHist_pairwise`: so the history the log records, the boot state then `admStates`
  (`srvHist`), is strictly ordered, with no state twice (`srvHist_nodup`).
- `srvHist_eq_of_prefix`: a prefix of a history of the log that ends where another history of
  the log does is that history (what pins the store's history, below the cap, to the applied log's).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ProposeOn
public import Proof.go_etcd_io.etcd.server.v3.auth.Boot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **A state's order** (H5): twice its revision, plus one if enabled. -/
def authOrd (st : auth.AuthState) : Nat := 2 * st.revision + (if st.enabled then 1 else 0)

/-- A step whose next state is a bump of `s` raises the order. -/
theorem authOrd_bump (st s : auth.AuthState) (h : st.revision ≤ s.revision) :
    authOrd st < authOrd (auth.bump s) := by
  unfold authOrd auth.bump
  simp only
  split <;> split <;> omega

/-- **An admitted admin step that changes the state raises its order.** -/
theorem adminStateR_ord (rq : apply.IRRModel) (st st' : auth.AuthState)
    (h : adminStateR rq st st') (hne : st' ≠ st) : authOrd st < authOrd st' := by
  unfold adminStateR at h
  split at h
  · split at h
    all_goals first
      | exact absurd h hne
      | skip
    · split at h
      · rcases h with ⟨-, h⟩ | ⟨o, ho, rfl⟩
        · exact absurd h hne
        · simp only [auth.stepOf, auth.userAddF] at ho
          subst ho
          split
          · simp_all [outState]
          split
          · simp_all [outState]
          · exact authOrd_bump st _ (by simp [auth.putUser])
      · exact absurd h hne
    · split at h
      · obtain ⟨o, ho, rfl⟩ := h
        simp only [auth.stepOf, auth.roleAddF] at ho
        subst ho
        split
        · simp_all [outState]
        split
        · simp_all [outState]
        · exact authOrd_bump st _ (by simp [auth.putRole])
      · exact absurd h hne
    · split at h
      · obtain ⟨o, ho, rfl⟩ := h
        simp only [auth.userGrantRoleR] at ho
        split at ho
        · subst ho; simp_all [outState]
        · split at ho
          · subst ho; simp_all [outState]
          · split at ho
            · subst ho; simp_all [outState]
            · obtain ⟨u', -, -, rfl⟩ := ho
              exact authOrd_bump st _ (by simp [auth.putUser])
      · exact absurd h hne
    · split at h
      · obtain ⟨o, ho, rfl⟩ := h
        simp only [auth.roleGrantPermissionR] at ho
        split at ho
        · subst ho; simp_all [outState]
        · split at ho
          · subst ho; simp_all [outState]
          · split at ho
            · subst ho; simp_all [outState]
            · subst ho
              exact authOrd_bump st _ (by simp [auth.putRole])
      · exact absurd h hne
    · obtain ⟨o, ho, rfl⟩ := h
      simp only [auth.stepOf, auth.authEnableF] at ho
      subst ho
      split
      · simp_all [outState]
      · rename_i hen
        split
        · simp_all [outState]
        · split
          · unfold authOrd outState
            simp only [Bool.not_eq_true] at hen
            simp [hen]
          · simp_all [outState]
  · exact absurd h hne

/-- **The model's admin step, where it changes the state, raises its order.** -/
theorem adminNext_ord (rq : apply.IRRModel) (st : auth.AuthState) (hne : adminNext rq st ≠ st) :
    authOrd st < authOrd (adminNext rq st) := by
  unfold adminNext at hne ⊢
  split
  · rename_i hd
    rw [dif_pos hd] at hne
    exact adminStateR_ord rq st _ (Classical.choose_spec hd).1 hne
  · rename_i hd
    rw [dif_neg hd] at hne
    simp_all [outState]

/-- **The history the log `L` records** (H5): the store's boot state, then `admStates` from the
start's state `bump bootState` (the store's history at the start is `[bootState, bump bootState]`). -/
def srvHist (γk : KVNames) (L : List EntryModel) : List auth.AuthState :=
  auth.bootState :: admStates γk (auth.bump auth.bootState) L

theorem srvHist_nil (γk : KVNames) :
    srvHist γk [] = [auth.bootState, auth.bump auth.bootState] := rfl

theorem srvHist_last (γk : KVNames) (L : List EntryModel) :
    (srvHist γk L).getLast? = some (srvAuthAtLog γk (auth.bump auth.bootState) L) := by
  unfold srvHist
  rw [List.getLast?_cons, admStates_last]
  rfl

/-- Appending `x` above the last element keeps a list strictly ordered. -/
theorem pairwise_ord_snoc (l : List auth.AuthState) (z x : auth.AuthState)
    (hl : l.Pairwise (fun a b => authOrd a < authOrd b)) (hz : l.getLast? = some z)
    (hx : authOrd z < authOrd x) :
    (l ++ [x]).Pairwise (fun a b => authOrd a < authOrd b) := by
  rw [List.pairwise_append]
  refine ⟨hl, List.pairwise_singleton _ _, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst hb
  obtain ⟨ys, hl'⟩ := List.getLast?_eq_some_iff.mp hz
  rw [hl'] at ha hl
  rw [List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · rw [List.pairwise_append] at hl
    exact Nat.lt_trans (hl.2.2 a ha z (List.mem_singleton_self _)) hx
  · exact hx

/-- **The history the log records is strictly ordered.** -/
theorem srvHist_pairwise (γk : KVNames) (L : List EntryModel) :
    (srvHist γk L).Pairwise (fun a b => authOrd a < authOrd b) := by
  suffices h : ∀ R : List EntryModel,
      (srvHist γk R.reverse).Pairwise (fun a b => authOrd a < authOrd b) by
    simpa using h L.reverse
  intro R
  induction R with
  | nil =>
    simp only [List.reverse_nil]
    rw [srvHist_nil]
    simp [authOrd, auth.bump, auth.bootState]
  | cons m R ih =>
    rw [List.reverse_cons]
    by_cases ha : admEntry γk.c0 (srvAuthAtLog γk (auth.bump auth.bootState) R.reverse) m
    · unfold srvHist at ih ⊢
      rw [admStates_snoc_adm _ _ _ _ ha, ← List.cons_append]
      apply pairwise_ord_snoc _ _ _ ih
      · rw [List.getLast?_cons, admStates_last]
      · obtain ⟨ht, hd, rq, hdec, hv, hna, -, hne⟩ := ha
        rw [srvAuthAtLog_snoc_adm _ _ _ _ rq ht hd hdec hv hna]
        exact adminNext_ord rq _ hne
    · unfold srvHist at ih ⊢
      rw [admStates_snoc_other _ _ _ _ ha]
      exact ih

theorem srvHist_nodup (γk : KVNames) (L : List EntryModel) : (srvHist γk L).Nodup :=
  (srvHist_pairwise γk L).imp (fun h => Nat.ne_of_lt h ∘ congrArg authOrd)

/-- **Two prefixes of a list with no element twice that end at the same element are equal.** -/
theorem prefix_eq_of_last {α : Type} (l h1 h2 : List α) (hn : l.Nodup) (p1 : h1 <+: l)
    (p2 : h2 <+: l) (hl : h1.getLast? = h2.getLast?) (h1n : h1 ≠ []) : h1 = h2 := by
  -- the two prefixes are comparable; the shorter one is a prefix of the longer
  have hc : h1 <+: h2 ∨ h2 <+: h1 := by
    rcases Nat.le_total h1.length h2.length with h | h
    · exact Or.inl (List.prefix_of_prefix_length_le p1 p2 h)
    · exact Or.inr (List.prefix_of_prefix_length_le p2 p1 h)
  have key : ∀ a b : List α, a <+: b → b <+: l → a ≠ [] → a.getLast? = b.getLast? → a = b := by
    intro a b hab hbl ha hlast
    obtain ⟨t, rfl⟩ := hab
    cases t with
    | nil => simp
    | cons y t =>
      exfalso
      obtain ⟨z, hz⟩ : ∃ z, a.getLast? = some z := by
        cases h : a.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp h) ha
        | some z => exact ⟨z, rfl⟩
      have hb : (a ++ y :: t).getLast? = some z := by rw [← hlast, hz]
      have hnb : (a ++ y :: t).Nodup := hbl.sublist.nodup hn
      have hza : z ∈ a := List.mem_of_getLast? hz
      have hzt : z ∈ y :: t := by
        rw [List.getLast?_append, List.getLast?_cons] at hb
        simp at hb
        exact List.mem_of_getLast? (by rw [List.getLast?_cons, hb])
      rw [List.nodup_append] at hnb
      exact hnb.2.2 z hza z hzt rfl
  rcases hc with h | h
  · exact key h1 h2 h p2 h1n hl
  · have h2n : h2 ≠ [] := by
      intro he; rw [he] at hl; simp at hl; exact h1n hl
    exact (key h2 h1 h p1 h2n hl.symm).symm

end pure

end EtcdGrove
end Perennial
