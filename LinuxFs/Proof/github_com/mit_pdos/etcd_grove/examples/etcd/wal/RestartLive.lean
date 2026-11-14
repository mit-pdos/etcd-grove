/-
Lean-first (no Rocq counterpart).

# The member's fields after a restart (W4c U5, `member.restart`)

`tMemFields_read`: the raft-like fields `resume` sets from a well-formed history's read (`tRead img = some
c`) meet `tMemFields` (`MemberInv.lean`): the read term (`tResumeTerm c`) and every term `tResumeTerms c`
records below `2^63`. The hard state's term is the last save's (bounded by `tOpWf`'s third clause), the base
term a snapshot's or 0, the entries' terms `tEntWf`'s.
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RestartOk
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.MemberInv
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Resume

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI

section pure
variable [GooseExts]

theorem foldl_tHsStep_term : ∀ (l : List TOp) (p : THs), uint.nat p.term' < 2 ^ 63 →
    (∀ o ∈ l, tOpWf o) → uint.nat (l.foldl tHsStep p).term' < 2 ^ 63 := by
  intro l
  induction l with
  | nil => intro p hp _; exact hp
  | cons o l ih =>
    intro p hp hl
    simp only [List.foldl_cons]
    apply ih _ _ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    unfold tHsStep tPhsNext
    split
    · exact hp
    · rename_i hsn
      split
      · exact hp
      · exact (hl o (List.mem_cons_self ..)).2.2 (by simpa using hsn)

theorem tLastHS_term {h : List TOp} (hw : tHistWf h) : uint.nat (tLastHS h).term' < 2 ^ 63 :=
  foldl_tHsStep_term h tHs0 (by simp [tHs0]) hw

theorem tFoldChkFrom_baseTerm : ∀ (L : List TOp) (s s' : TContents), tFoldChkFrom s L = some s' →
    uint.nat s.baseTerm < 2 ^ 63 → (∀ o ∈ L, tOpWf o) → uint.nat s'.baseTerm < 2 ^ 63 := by
  intro L
  induction L with
  | nil => intro s s' h hs _; simp [tFoldChkFrom] at h; subst h; exact hs
  | cons o L ih =>
    intro s s' h hs hL
    unfold tFoldChkFrom at h
    split at h
    · rename_i hsn
      refine ih _ s' h ?_ (fun x hx => hL x (List.mem_cons_of_mem _ hx))
      unfold tSaveSnap
      split
      · exact hs
      · exact ((hL o (List.mem_cons_self ..)).1 hsn).2
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ents, -, h⟩ := h
      exact ih _ s' h hs (fun x hx => hL x (List.mem_cons_of_mem _ hx))

theorem tRead_baseTerm {h : List TOp} {c : TContents} (hw : tHistWf h) (hr : tRead h = some c) :
    uint.nat c.baseTerm < 2 ^ 63 := by
  unfold tRead tFoldChk at hr
  exact tFoldChkFrom_baseTerm _ tC0 c hr (by simp [tC0]) (fun o ho => hw o (List.mem_filter.1 ho).1)

theorem tResumeTerms_ok_gen : ∀ (es : List TEnt) (M : GMap w64 w64), tTermsOk M →
    (∀ e ∈ es, tEntWf e) → tTermsOk (es.foldl (fun M e => <[e.index' := e.term']> M) M) := by
  intro es
  induction es with
  | nil => intro M hM _; exact hM
  | cons e es ih =>
    intro M hM hes
    simp only [List.foldl_cons]
    exact ih _ (tTermsOk_insert hM _ _ (hes e (List.mem_cons_self ..)).2.2.2)
      (fun x hx => hes x (List.mem_cons_of_mem _ hx))

/-- **The fields a well-formed history's read resumes meet `tMemFields`.** -/
theorem tMemFields_read {img : List TOp} {c : TContents} (hw : tHistWf img) (hr : tRead img = some c) :
    tMemFields (tResumeTerm c) (tResumeTerms c) := by
  refine ⟨?_, ?_⟩
  · unfold tResumeTerm
    split
    · simp
    · rw [tRead_hs hr]; exact tLastHS_term hw
  · exact tResumeTerms_ok_gen _ _ (tTermsOk_insert tTermsOk_empty _ _ (tRead_baseTerm hw hr))
      (tRead_ents_wf hw hr)

end pure

end etcd_wal
end EtcdGrove
end Perennial
