/-
Lean-first (no Rocq counterpart).

# k8s-dist K4: a step's answer on renamed stores

`notes/k8s-dist-k4.md`, "Handoff K4-3", step 1. The search's store `⟨its, a⟩` and the cluster's
`⟨its.map (renItem ρ), b⟩`, `a ≤ b`: when the cluster's step answers `y` (`mstepL`'s `.2`), the search's
answers `y` too, given what the operation's anchors (`OpAnchors`) and the search's target (`targetL`)
give (`AnsRen`). A "not found" and a new object pin `a = b`; an object or a precondition's message an
answer shows is anchored, so not renamed (`renObj_fix`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedRename

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)

section go
variable [GooseExts]

/-- **What the step's answer needs** of the renaming, the stores and the cluster's answer `y`: the
renaming fixes 0 and cuts every stored revision like the identity (below `2^64`); a resource-version
precondition is an anchor; the search's store is at most the cluster's; and from `y`'s anchors and the
search's target: a successful answer's revision and the object of a failed resource-version
precondition's message are anchors, a "not found"'s revision is at most the search's, a successful
write's revision at most the next one, a successful read's minimum revision at most the search's. -/
structure AnsRen (A : List Nat) (ρ : Nat → Nat) (x : Input) (its : List item) (a b : w64) (y : Output) :
    Prop where
  zero : ρ 0 = 0
  cut : ∀ it ∈ its, CutW A ρ (uint.nat it.obj'.ResourceVersion')
  fits : ∀ it ∈ its, ρ (uint.nat it.obj'.ResourceVersion') < 2 ^ 64
  pre : x.HasPreRV' = true → ∀ r, parseRVD x.PreRV' = some r → uint.nat r ∈ A
  le : uint.nat a ≤ uint.nat b
  b_lt : uint.nat b + 1 < 2 ^ 64
  rvA : y.Err' = W64 0 → uint.nat y.RV' ∈ A
  msgA : ∀ o : Obj, y.ErrMsg' = preMsgL x o → (x.HasPreUID' && !decide (x.PreUID' = o.UID')) = false →
    uint.nat o.ResourceVersion' ∈ A
  nf : y.Err' = W64 1 → uint.nat y.ErrRV' ≤ uint.nat a
  wr : y.Err' = W64 0 → isWriteL x = true → uint.nat y.RV' ≤ uint.nat a + 1
  rd : y.Err' = W64 0 → isWriteL x = false → ∀ req, parseRVD x.MinRV' = some req →
    uint.nat req ≤ uint.nat a

section ans
variable {A : List Nat} {ρ : Nat → Nat} {x : Input} {its : List item} {a b : w64}

/-- The preconditions on a stored object are the same renamed (`preOkL_ren`, the precondition's
revision an anchor: `CutW.eq_iff`). -/
theorem AnsRen.preOk {y : Output} (h : AnsRen A ρ x its a b y) (it : item) (hi : it ∈ its) :
    preOkL x (renObj ρ it.obj') = preOkL x it.obj' :=
  preOkL_ren ρ x _ (h.fits it hi) (fun hp r hr => (h.cut it hi).eq_iff (h.pre hp r hr))

/-- A "not found" at the cluster's revision pins the search's store to it. -/
theorem AnsRen.nf_eq (k : GoString) (h : AnsRen A ρ x its a b (notFoundL b k)) : a = b := by
  have := h.nf (by simp [notFoundL, errOutL])
  simp only [notFoundL, errOutL] at this
  have := h.le; word

/-- A write's new object at the cluster's next revision pins the search's store to the cluster's. -/
theorem AnsRen.new_eq (o : Obj) (h : AnsRen A ρ x its a b (objOutL o)) (hw : isWriteL x = true)
    (ho : o.ResourceVersion' = b + W64 1) : a = b := by
  have := h.wr (by simp [objOutL]) hw
  simp only [objOutL, ho] at this
  have := h.le; have := h.b_lt; word

/-- A shown stored object is not renamed. -/
theorem AnsRen.obj_fix (it : item) (hi : it ∈ its) (h : AnsRen A ρ x its a b (objOutL (renObj ρ it.obj'))) :
    renObj ρ it.obj' = it.obj' :=
  renObj_fix _ (h.cut it hi) (h.fits it hi) (by have := h.rvA (by simp [objOutL]); simpa [objOutL] using this)

/-- A failed precondition's message on a stored object is the same renamed. -/
theorem AnsRen.msg_fix (k : GoString) (it : item) (hi : it ∈ its)
    (h : AnsRen A ρ x its a b (invalidObjL k (preMsgL x (renObj ρ it.obj')))) :
    preMsgL x (renObj ρ it.obj') = preMsgL x it.obj' := by
  rcases Bool.eq_false_or_eq_true (x.HasPreUID' && !decide (x.PreUID' = it.obj'.UID')) with hu | hu
  · exact preMsgL_ren_uid ρ x _ hu
  · have hA := h.msgA (renObj ρ it.obj') (by simp [invalidObjL, invalidOutL]) hu
    rw [renObj_fix _ (h.cut it hi) (h.fits it hi) hA]

/-- An object with a new revision forgets the renaming. -/
theorem renObj_with_rv (o : Obj) (r : w64) :
    { renObj ρ o with ResourceVersion' := r } = { o with ResourceVersion' := r } := rfl

theorem mcreateL_ans_ren (hw : isWriteL x = true)
    (h : AnsRen A ρ x its a b (mcreateL x ⟨its.map (renItem ρ), b⟩).2) :
    (mcreateL x ⟨its, a⟩).2 = (mcreateL x ⟨its.map (renItem ρ), b⟩).2 := by
  unfold mcreateL at h ⊢
  simp only [lookupL_ren ρ h.zero] at h ⊢
  by_cases hk : (lookupL its x.Key').2 = true
  · simp only [hk, if_true]
  · simp only [hk, Bool.false_eq_true, if_false] at h ⊢
    obtain rfl := h.new_eq _ hw (by rfl)
    rfl

theorem mdeleteL_ans_ren (hw : isWriteL x = true)
    (h : AnsRen A ρ x its a b (mdeleteL x ⟨its.map (renItem ρ), b⟩).2) :
    (mdeleteL x ⟨its, a⟩).2 = (mdeleteL x ⟨its.map (renItem ρ), b⟩).2 := by
  unfold mdeleteL at h ⊢
  simp only [lookupL_ren ρ h.zero, renItem_obj, renObj_node] at h ⊢
  by_cases hk : (lookupL its x.Key').2 = true
  · have hi := lookupL_mem its x.Key' hk
    simp only [hk, Bool.not_true, Bool.false_eq_true, if_false, h.preOk _ hi] at h ⊢
    rcases Bool.eq_false_or_eq_true (preOkL x (lookupL its x.Key').1.obj') with hp | hp
    · simp only [hp, Bool.not_true, Bool.false_eq_true, if_false] at h ⊢
      rcases Bool.eq_false_or_eq_true (rejects x.HasReject' x.Reject' (lookupL its x.Key').1.obj'.Node')
        with hr | hr
      · simp only [hr, if_true]
      · simp only [hr, Bool.false_eq_true, if_false] at h ⊢
        obtain rfl := h.new_eq _ hw (by rfl)
        rfl
    · simp only [hp, Bool.not_false, if_true] at h ⊢
      rw [h.msg_fix _ _ hi]
  · simp only [Bool.not_eq_true] at hk
    simp only [hk, Bool.not_false, if_true] at h ⊢
    obtain rfl := h.nf_eq _
    rfl

theorem mupdateL_ans_ren (hw : isWriteL x = true)
    (h : AnsRen A ρ x its a b (mupdateL x ⟨its.map (renItem ρ), b⟩).2) :
    (mupdateL x ⟨its, a⟩).2 = (mupdateL x ⟨its.map (renItem ρ), b⟩).2 := by
  unfold mupdateL at h ⊢
  simp only [lookupL_ren ρ h.zero, renItem_obj, renItem_canon] at h ⊢
  by_cases hk : (lookupL its x.Key').2 = true
  · have hi := lookupL_mem its x.Key' hk
    simp only [hk, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false, if_true, h.preOk _ hi,
      renObj_node, updatedL_ren, sameObjL_ren, true_and] at h ⊢
    rcases Bool.eq_false_or_eq_true (preOkL x (lookupL its x.Key').1.obj') with hp | hp
    · simp only [hp, Bool.not_true, Bool.false_eq_true, if_false] at h ⊢
      rcases Bool.eq_false_or_eq_true (rejects x.HasReject' x.Reject' (lookupL its x.Key').1.obj'.Node')
        with hr | hr
      · simp only [hr, if_true]
      · simp only [hr, Bool.false_eq_true, if_false] at h ⊢
        by_cases hs : sameObjL (updatedL x (lookupL its x.Key').1.obj') (lookupL its x.Key').1.obj' = true ∧
            (lookupL its x.Key').1.canon' = true
        · simp only [hs, and_self, if_true] at h ⊢
          rw [h.obj_fix _ hi]
        · simp only [hs, if_false] at h ⊢
          obtain rfl := h.new_eq _ hw (by rfl)
          rfl
    · simp only [hp, Bool.not_false, if_true] at h ⊢
      rw [h.msg_fix _ _ hi]
  · simp only [Bool.not_eq_true] at hk
    simp only [hk, Bool.not_false, Bool.true_and, Bool.false_eq_true, if_false, false_and] at h ⊢
    rcases Bool.eq_false_or_eq_true x.IgnoreNotFound' with hn | hn
    · simp only [hn, Bool.not_true, Bool.false_eq_true, if_false] at h ⊢
      rcases Bool.eq_false_or_eq_true (preOkL x zObj) with hp | hp
      · simp only [hp, Bool.not_true, Bool.false_eq_true, if_false] at h ⊢
        rcases Bool.eq_false_or_eq_true (rejects x.HasReject' x.Reject' zObj.Node') with hr | hr
        · simp only [hr, if_true]
        · simp only [hr, Bool.false_eq_true, if_false] at h ⊢
          obtain rfl := h.new_eq _ hw (by rfl)
          rfl
      · simp only [hp, Bool.not_false, if_true]
    · simp only [hn, Bool.not_false, if_true] at h ⊢
      obtain rfl := h.nf_eq _
      rfl

theorem mgetL_ans_ren (hr : isWriteL x = false) (h : AnsRen A ρ x its a b (mgetL x ⟨its.map (renItem ρ), b⟩)) :
    mgetL x ⟨its, a⟩ = mgetL x ⟨its.map (renItem ρ), b⟩ := by
  unfold mgetL at h ⊢
  simp only [lookupL_ren ρ h.zero, renItem_obj] at h ⊢
  cases hq : parseRVD x.MinRV' with
  | none => rfl
  | some req =>
    simp only [hq] at h ⊢
    by_cases hb : uint.nat b < uint.nat req
    · have : uint.nat a < uint.nat req := Nat.lt_of_le_of_lt h.le hb
      simp only [hb, this, if_true]
    · simp only [hb, if_false] at h ⊢
      by_cases hk : (lookupL its x.Key').2 = true
      · have hi := lookupL_mem its x.Key' hk
        simp only [hk, Bool.not_true, Bool.false_eq_true, if_false] at h ⊢
        have hreq := h.rd (by simp [objOutL]) hr req hq
        simp only [show ¬ uint.nat a < uint.nat req by omega, if_false]
        rw [h.obj_fix _ hi]
      · simp only [Bool.not_eq_true] at hk
        simp only [hk, Bool.not_false, if_true] at h ⊢
        rcases Bool.eq_false_or_eq_true x.IgnoreNotFound' with hn | hn
        · simp only [hn, if_true] at h ⊢
          have hreq := h.rd (by simp [zeroOutL, errOutL]) hr req hq
          simp only [show ¬ uint.nat a < uint.nat req by omega, if_false]
        · simp only [hn, Bool.false_eq_true, if_false] at h ⊢
          obtain rfl := h.nf_eq _
          simp only [hb, if_false]

/-- **A step's answer on renamed stores** (`notes/k8s-dist-k4.md`, "Handoff K4-3", step 1): the
search's store answers what the cluster's does. -/
theorem mstepL_ans_ren (h : AnsRen A ρ x its a b (mstepL x ⟨its.map (renItem ρ), b⟩).2) :
    (mstepL x ⟨its, a⟩).2 = (mstepL x ⟨its.map (renItem ρ), b⟩).2 := by
  unfold mstepL at h ⊢
  by_cases h0 : x.Kind' = W64 0
  · simp only [h0, if_true] at h ⊢
    exact mcreateL_ans_ren (by simp [isWriteL, h0]) h
  · simp only [h0, if_false] at h ⊢
    by_cases h1 : x.Kind' = W64 1
    · simp only [h1, if_true] at h ⊢
      exact mdeleteL_ans_ren (by simp [isWriteL, h1]) h
    · simp only [h1, if_false] at h ⊢
      by_cases h2 : x.Kind' = W64 2
      · simp only [h2, if_true] at h ⊢
        exact mupdateL_ans_ren (by simp [isWriteL, h2]) h
      · simp only [h2, if_false] at h ⊢
        exact mgetL_ans_ren (by simp only [isWriteL, h0, h1, h2, decide_false, Bool.or_false]) h

end ans

end go

end k8s_dist
end EtcdGrove
end Perennial
