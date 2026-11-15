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

/-- `resume`'s last index, as the last entry's. -/
theorem tResumeLast_eq (l : List TEnt) (x : w64) :
    l.foldl (fun _ e => e.index') x = (l.getLast?.map (·.index')).getD x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    cases l with
    | nil => rfl
    | cons b l => simp [List.getLast?_eq_getLast (List.cons_ne_nil b l)]

/-- **After a restart, the member's fields are the disciplined history's fold**: the image read,
disciplined from its own read (`ReadsBack.tSim_restartRead`), with `resume`'s fields. -/
theorem tRestart_sim {o : TOracle} {cd : TCand} {d : WalDur} {img : List TOp} {c : TContents}
    (hok : tCandOk o cd d) (hI : d.H.map WalOpG.toM = img.map absOp) (hr : tRead img = some c) :
    tSim (img.map absOp) img.length ∧ ∃ σ, tSimAt (img.map absOp) img.length σ ∧
      σ.b = uint.nat c.baseIdx ∧ σ.last = uint.nat (tResumeLast c) ∧ σ.commit = uint.nat (tResumeCommit c) := by
  have hw : walImg ((tCandHist o cd).map absOp) (tCandMark o cd) (img.map absOp) := hI ▸ hok.1
  have ha := tRead_abs img
  rw [hr, Option.map_some] at ha
  obtain ⟨σ, hσ, hpc⟩ := Option.map_eq_some_iff.1 ha.symm
  obtain ⟨-, hsa⟩ := tSim_restartRead hok.2.2.2.2.2.2 hw hσ
  rw [List.length_map] at hsa
  have hcl := tSimAt_commitLe hsa
  have hwf : walEntsWf σ := walReadCut_wf (k := 0) (by rw [walReadCut_zero]; exact hσ)
  simp only [projC, absC, Prod.mk.injEq] at hpc
  obtain ⟨hhs, hbi, -, hents⟩ := hpc
  have hb : σ.b = uint.nat c.baseIdx := by simp only [StorContents.b, hbi]
  have hlast : σ.last = uint.nat (tResumeLast c) := by
    unfold tResumeLast
    rw [tResumeLast_eq]
    cases hl : c.ents.getLast? with
    | none =>
      have : c.ents = [] := List.getLast?_eq_none_iff.1 hl
      simp only [StorContents.last, hents, this, List.map_nil, List.length_nil, Option.map_none,
        Option.getD_none, hb, Nat.add_zero]
    | some e =>
      simp only [Option.map_some, Option.getD_some]
      have hne : c.ents ≠ [] := by intro h0; rw [h0] at hl; cases hl
      have hlen : 0 < c.ents.length := by
        cases h : c.ents with
        | nil => exact absurd h hne
        | cons _ _ => simp
      have hx : c.ents[c.ents.length - 1]? = some e := by
        rw [List.getLast?_eq_getElem?] at hl; exact hl
      have hx' : σ.ents[c.ents.length - 1]? = some (absEnt e) := by
        rw [hents, List.getElem?_map, hx]; rfl
      have := hwf _ _ hx'
      have hl2 : σ.ents.length = c.ents.length := by rw [hents, List.length_map]
      simp only [StorContents.last]
      show σ.b + σ.ents.length = uint.nat (absEnt e).Index'
      omega
  refine ⟨tSimAt_tSim hsa, σ, hsa, hb, hlast, ?_⟩
  have hc : σ.commit = uint.nat c.hs.commit' := by simp only [StorContents.commit, hhs]; rfl
  unfold tResumeCommit
  rw [if_neg (by omega)]; exact hc

end pure

end etcd_wal
end EtcdGrove
end Perennial
