/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLa/Inv.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-a: **the tag-bound invariant** over runs (`tinv`): in every reachable configuration, every
tag carried (stores, `prevValTag`, copies' bases and recovery candidates, coordinator records,
messages in flight) has `0 ≤ ts ≤ Tc c ≤ 72` and `0 ≤ rmwc ≤ El l < 9 · 2^21`.
-/
module

public import Dsverify.Proof.gryff.PureLa.Post
public import Dsverify.Proof.gryff.PureL.CfgInv

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.La

open model kahn Perennial.gryff.pure

def stA (c : Cfg gNet) (j : Fin 3) : RState := c.st j
def infA (c : Cfg gNet) (j : Fin 3) : List Msg := c.inflight j

/-- The `ts` bound: the replicas' potentials. -/
def Tc (c : Cfg gNet) : Int := Pot (stA c 0) + Pot (stA c 1) + Pot (stA c 2)

/-- The `rmwc` bound: the executions with a result so far. -/
noncomputable def El (l : List Label) : Int :=
  ((execSeq 0 (projR l 0)).length + (execSeq 1 (projR l 1)).length +
    (execSeq 2 (projR l 2)).length : Nat)

/-- **The tag-bound invariant.** -/
structure Inv (l : List Label) (c : Cfg gNet) : Prop where
  srt : ∀ j, Srt (stA c j).wops
  nr : ∀ j, (stA c j).nReqs ≤ 24
  t0 : 0 ≤ Tc c
  sb : ∀ j, SB (Tc c) (El l) (stA c j)
  mb : ∀ j, ∀ m ∈ infA c j, MB (Tc c) (El l) m

theorem pot_le (s : RState) : Pot s ≤ s.nReqs := by unfold Pot; omega

theorem Tc_le {c : Cfg gNet} (h : ∀ j, (stA c j).nReqs ≤ 24) : Tc c ≤ 72 := by
  have := pot_le (stA c 0); have := pot_le (stA c 1); have := pot_le (stA c 2)
  have := h 0; have := h 1; have := h 2
  unfold Tc; omega

theorem El_nonneg (l : List Label) : 0 ≤ El l := by unfold El; omega

theorem El_le {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) :
    El l ≤ 9 * 2 ^ 21 := by
  have h0 := execSeq_len 0 _ (exec_nodup h 0)
  have h1 := execSeq_len 1 _ (exec_nodup h 1)
  have h2 := execSeq_len 2 _ (exec_nodup h 2)
  unfold El; omega

theorem Tc_step {c c' : Cfg gNet} {i : Fin 3} {s' : RState}
    (hst : ∀ j, stA c' j = if j = i then s' else stA c j) :
    Tc c' = Tc c + (Pot s' - Pot (stA c i)) := by
  unfold Tc; rw [hst 0, hst 1, hst 2]
  rcases i with ⟨i, hi⟩
  rcases i with _ | _ | _ | i
  · simp; omega
  · simp; omega
  · simp; omega
  · omega

theorem stOf_run {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r : Fin 3) :
    stOf r (projR l r) = c.st r := by
  obtain ⟨cn, h1, h2, h3⟩ := grun_cut h l.length
  have e1 : l.take l.length = l := List.take_length
  have e2 : l.drop l.length = [] := List.drop_length
  have h2' := grun_of_eq e2 h2
  cases h2'
  obtain ⟨o, ho⟩ := h3 r
  rw [e1] at ho
  exact stOf_of_runP ho

theorem El_step {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {i : Fin 3}
    {e : Ev} {s' : RState} {o : List Out} (hstep : stepR i (c.st i) e = .ok (s', o)) :
    El (l ++ [(i, e)]) = El l + (dEx e o : Int) := by
  have key : ∀ r : Fin 3, (execSeq r (projR (l ++ [(i, e)]) r)).length =
      (execSeq r (projR l r)).length + if i = r then dEx e o else 0 := by
    intro r
    rw [proj_snoc]
    split
    · rename_i hir; subst hir
      rw [execSeq_snoc, stOf_run h, hstep]
    · simp
  unfold El
  rw [key 0, key 1, key 2]
  rcases i with ⟨i, hi⟩
  rcases i with _ | _ | _ | i
  · simp; omega
  · simp; omega
  · simp; omega
  · omega

theorem mem_sentTo {j : Fin 3} {o : List Out} {m : Msg} (h : m ∈ kahn.sentTo gNet j o) :
    Out.send j m ∈ o := by
  unfold kahn.sentTo at h
  obtain ⟨x, hx, hx'⟩ := List.mem_filterMap.1 h
  cases x with
  | send d m' =>
    simp only at hx'
    split at hx'
    · cases hx'; subst_vars; exact hx
    · cases hx'
  | ext _ => cases hx'

theorem toOption_ok' {r : StepRes} {a : RState × List Out} (h : Except.toOption r = some a) :
    r = .ok a := by
  cases r <;> simp_all [Except.toOption]

theorem mem_consume' {r : Option Msg} {l : List Msg} {m : Msg} (h : m ∈ consume r l) : m ∈ l := by
  cases r with
  | none => exact h
  | some a => exact List.mem_of_mem_erase h

theorem inv_init : Inv [] (Cfg.init gNet) := by
  have hs : ∀ j : Fin 3, stA (Cfg.init gNet) j = RState.init j.val := fun _ => rfl
  have hT : Tc (Cfg.init gNet) = 0 := by
    unfold Tc; rw [hs 0, hs 1, hs 2]; rfl
  have hE : El [] = 0 := rfl
  refine ⟨fun j => ?_, fun j => ?_, by rw [hT]; exact Int.le_refl 0, fun j => ?_, fun j m hm => ?_⟩
  · rw [hs]; exact List.Pairwise.nil
  · rw [hs]; simp [RState.init]
  · rw [hs, hT, hE]
    refine ⟨TB_tag0 (Int.le_refl _) (Int.le_refl _), fun v hv => ?_,
      fun q i c hc => ?_, fun e he => ?_, fun e he => ?_⟩
    · cases hv
    · cases hc
    · cases he
    · cases he
  · cases hm

theorem stA_eq_i {c c' : Cfg gNet} {i : Fin 3} {s' : RState}
    (hst : c'.st = fun j => if j = i then s' else c.st j) : stA c' i = s' := by
  unfold stA; rw [hst]; simp

theorem stA_eq_ne {c c' : Cfg gNet} {i j : Fin 3} {s' : RState}
    (hst : c'.st = fun j => if j = i then s' else c.st j) (hj : j ≠ i) : stA c' j = stA c j := by
  unfold stA; rw [hst]; exact if_neg hj

theorem inv_step {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {xx : List Ext}
    (h : GRun (Cfg.init gNet) l c) (hi : Inv l c) (hs : GStep c i e c' xx) :
    Inv (l ++ [(i, e)]) c' := by
  obtain ⟨s', o, hstep, hmem, -, hst, hinf⟩ := hs
  have hstep' : stepR i (c.st i) e = .ok (s', o) := toOption_ok' hstep
  have hst' : ∀ j, stA c' j = if j = i then s' else stA c j := fun j => congrFun hst j
  have hT72 := Tc_le hi.nr
  have hE2 := El_le h
  obtain ⟨T', h1, h2, h3, h4, h5, h6⟩ := step_post (hi.sb i) (fun m hm => hi.mb i m (hmem m hm))
    (hi.srt i) (hi.nr i) hi.t0 hT72 (El_nonneg l) (by omega) hstep'
  have hTc := Tc_step hst'
  have hEl := El_step h hstep'
  have hT'le : T' ≤ Tc c' := by rw [hTc]; omega
  have hTle : Tc c ≤ Tc c' := by rw [hTc]; omega
  have hEle : El l ≤ El (l ++ [(i, e)]) := by rw [hEl]; omega
  have hE'le : El l + (dEx e o : Int) ≤ El (l ++ [(i, e)]) := by rw [hEl]; omega
  refine ⟨fun j => ?_, fun j => ?_, by have := hi.t0; omega, fun j => ?_, fun j m hm => ?_⟩
  · by_cases hj : j = i
    · subst hj; rw [stA_eq_i hst]; exact h5
    · rw [stA_eq_ne hst hj]; exact hi.srt j
  · by_cases hj : j = i
    · subst hj; rw [stA_eq_i hst]; exact h6
    · rw [stA_eq_ne hst hj]; exact hi.nr j
  · by_cases hj : j = i
    · subst hj; rw [stA_eq_i hst]; exact h3.mono hT'le hE'le
    · rw [stA_eq_ne hst hj]; exact (hi.sb j).mono hTle hEle
  · have hm2 : m ∈ c'.inflight j := hm
    rw [congrFun hinf j] at hm2
    rcases List.mem_append.1 hm2 with hm' | hm'
    · have : m ∈ infA c j := by
        split at hm'
        · exact mem_consume' hm'
        · exact hm'
      exact (hi.mb j m this).mono hTle hEle
    · exact (h4 _ (mem_sentTo hm')).mono hT'le hE'le

/-- **The tag-bound invariant holds along every run.** -/
theorem tinv {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) : Inv l c :=
  grun_inv Inv inv_init (fun _ _ _ _ _ _ h hi hs => inv_step h hi hs) l c h

/-- A write record's `maxValTag.ts` is at most 72. -/
theorem wops_ts {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r : Fin 3)
    {K : w64} {w : WriteOp} (hw : (c.st r).wops.get? K = some w) :
    sint.Z w.maxValTag.t.ts < 2 ^ 31 - 1 := by
  have hi := tinv h
  have := ((hi.sb r).wops _ (AMap.mem_of_get? hw)).1.ts1
  simp only at this
  have := Tc_le hi.nr
  omega

/-- At every cut of a run, `prevValTag`'s and every copy's base's `rmwc` are below `2^31 - 1`. -/
theorem rmwc_cut {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (n : Nat)
    (r : Fin 3) :
    (∀ pvt, (cutSt l n r).prevValTag = some pvt → sint.Z pvt.t.rmwc < 2 ^ 31 - 1) ∧
      ∀ q i cp, (cutSt l n r).inst q i = some cp → sint.Z cp.base.t.rmwc < 2 ^ 31 - 1 := by
  obtain ⟨cn, h1, -, -⟩ := grun_cut h n
  have he : cutSt l n r = cn.st r := stOf_run h1 r
  have hi := tinv h1
  have hb := El_le h1
  rw [he]
  refine ⟨fun pvt hp => ?_, fun q i cp hc => ?_⟩
  · have := ((hi.sb r).pvt pvt hp).r1; omega
  · have := ((hi.sb r).inst q i cp hc).1.r1; omega

end Perennial.gryff.pure.La
