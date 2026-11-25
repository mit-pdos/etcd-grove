/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureP/Stable.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit P: the pure facts behind the executor's laws (H-X-1 `trace_stable`, H-X-3 `trace_depsOk`).

* `stable_run`: along a replica's own run, its instances stay, and its committed copies stay
  committed with the same value (`CKeep`, and agreement `agree_run` between the cut where the
  prefix ends and the run's end).
* `depsOk_cfg'`: in a reachable configuration, a replica's committed copies have commands of the
  system's shape (`cmdsOk`, A2's `CopyOK`) and deps in the instance space (`PureP/Deps.lean`), and
  `crtInstance` is at most `SLOTS` (A2's budget).
-/
module

public import Dsverify.Proof.gryff.PureP.Keep
public import Dsverify.Proof.gryff.PureP.Deps
public import Dsverify.Proof.gryff.Pure.Agree
public import Dsverify.Proof.gryff.PureL.Run
public import Dsverify.Proof.gryff.PureT.EpBase
public import Dsverify.Proof.gryff.PureT.Total

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureP

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.pureA Perennial.gryff.kahn

/-- **Stability along a replica's own run.** -/
theorem stable_run {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (k : Fin 3)
    {t : List Ev} (hp : t <+: projR l k) :
    (∀ n cp, committedCopy (stOf k t) n = some cp → ∃ cp', committedCopy (stOf k (projR l k)) n = some cp' ∧
        cp'.cmds = cp.cmds ∧ cp'.seq = cp.seq ∧ cp'.deps = cp.deps ∧ cp'.base = cp.base) ∧
      (∀ q i : w32, ((stOf k t).inst q i).isSome → ((stOf k (projR l k)).inst q i).isSome) := by
  obtain ⟨o, ho⟩ := grun_state h k
  have ho' : runP gNet k (projR l k) = some (c.st k, o) := ho
  have et : t = (projR l k).take t.length := List.prefix_iff_eq_take.1 hp
  have hlen : t.length ≤ (projR l k).length := hp.length_le
  have hck : CKeep (stOf k t) (stOf k (projR l k)) := by
    have := runP_ckeep ho' (j := t.length) (k := (projR l k).length) hlen (Nat.le_refl _)
    rw [List.take_length, ← et] at this; exact this
  refine ⟨fun n cp hc => ?_, fun q i hs => ?_⟩
  · obtain ⟨-, hb, hn, hi, hst⟩ := pureA.AE.inst_of_cc hc
    obtain ⟨cp', hi', hst'⟩ := hck _ _ cp hi
    have hcc' : committedCopy (stOf k (projR l k)) n = some cp' := by
      rw [← hn]; exact pureA.AE.cc_of_inst hb hi' (hst' hst)
    refine ⟨cp', hcc', ?_⟩
    -- agreement between the cut where `t` ends and the run's end
    obtain ⟨m, hm⟩ := pureA.AE.st_cut (l := l) k (j := t.length) hlen
    rw [← et] at hm
    obtain ⟨cn, h1, h2, h3⟩ := grun_cut h m
    obtain ⟨o1, ho1⟩ := h3 k
    have ecn : stOf k t = cn.st k := by rw [hm]; exact stOf_of_runP ho1
    have ec : stOf k (projR l k) = c.st k := stOf_of_runP ho'
    rw [ecn] at hi
    rw [ec] at hi'
    have e := agree_run h1 h2 (Or.inl ⟨k, cp, hi, hst, rfl⟩) (Or.inl ⟨k, cp', hi', hst' hst, rfl⟩)
    simp only [Copy.ival, IVal.mk.injEq] at e
    obtain ⟨e1, e2, e3, e4⟩ := e
    exact ⟨e1.symm, e2.symm, e3.symm, e4.symm⟩
  · obtain ⟨cp, hcp⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨cp', hi', -⟩ := hck q i cp hcp
    rw [hi']; rfl

theorem toInt_le_toNat (x : w32) : x.toInt ≤ (x.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]; split <;> omega

/-- **Commands and `crtInstance` in range** (the parts of H-X-3 the totality invariant gives). -/
theorem depsOk_cfg {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (k : Fin 3) :
    (∀ n cp, committedCopy (c.st k) n = some cp → model.cmdsOk cp.cmds = true) ∧
      ∀ q : w32, sint.Z ((c.st k).crt q) ≤ model.SLOTS := by
  have I := (tot.inv_reach h).1
  refine ⟨fun n cp hc => ?_, fun q => ?_⟩
  · obtain ⟨-, -, -, hi, -⟩ := pureA.AE.inst_of_cc hc
    exact ((I k).inst _ _ _ hi).2.1
  · have hb : ((c.st k).crt q).toNat ≤ 24 := by
      by_cases hq : q.toNat < 3
      · have e : q = rid32 ⟨q.toNat, hq⟩ := by
          apply BitVec.eq_of_toNat_eq; simp [rid32]
        rw [e]
        exact Nat.le_trans ((I k).crt _) (tot.Pf_le I _)
      · have : (c.st k).crt q = 0 := by
          unfold RState.crt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by have := (I k).lcrt; omega)]; rfl
        rw [this]; decide
    have := toInt_le_toNat ((c.st k).crt q)
    show ((c.st k).crt q).toInt ≤ _
    simp only [model.SLOTS]; omega

/-- **H-X-3's pure content**: committed copies' dependencies in the instance space, their
commands of the system's shape, `crtInstance` at most `SLOTS`. -/
theorem depsOk_cfg' {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (k : Fin 3) :
    (∀ n cp, committedCopy (c.st k) n = some cp →
        (∀ j : Nat, j < 3 → sint.Z (cp.deps.at j) < model.SLOTS) ∧ model.cmdsOk cp.cmds = true) ∧
      ∀ q : w32, sint.Z ((c.st k).crt q) ≤ model.SLOTS := by
  obtain ⟨h1, h2⟩ := depsOk_cfg h k
  refine ⟨fun n cp hc => ⟨?_, h1 n cp hc⟩, h2⟩
  obtain ⟨-, -, -, hi, -⟩ := pureA.AE.inst_of_cc hc
  exact deps_reach h k hi

end Perennial.gryff.pureP
