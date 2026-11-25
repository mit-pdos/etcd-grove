/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureL/CfgInv.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L: invariants over configurations (with the messages in flight); the coordinator's write
records are in `WRec.lean`.

`grun_inv`: an invariant `I l c` of a run's labels so far and its configuration, kept by every
global step, holds along every run (and so at every cut: `grun_cut`).
-/
module

public import Dsverify.Proof.gryff.PureL.Store
public import Dsverify.Proof.gryff.PureL.F4

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

theorem grun_snoc_inv {c c' : Cfg gNet} {l : List Label} {x : Label}
    (h : GRun c (l ++ [x]) c') : ∃ c1 xx, GRun c l c1 ∧ GStep c1 x.1 x.2 c' xx := by
  obtain ⟨c1, h1, h2⟩ := grun_append h
  obtain ⟨c2, xx, hs, hr⟩ := grun_cons_inv h2
  cases hr
  exact ⟨c1, xx, h1, hs⟩

/-- **Invariants of runs**: kept by every step from a reachable configuration. -/
theorem grun_inv (I : List Label → Cfg gNet → Prop) (h0 : I [] (Cfg.init gNet))
    (hs : ∀ l c i e c' x, GRun (Cfg.init gNet) l c → I l c → GStep c i e c' x →
      I (l ++ [(i, e)]) c') :
    ∀ l c, GRun (Cfg.init gNet) l c → I l c := by
  intro l
  refine snoc_ind (P := fun l => ∀ c, GRun (Cfg.init gNet) l c → I l c) ?_ ?_ l
  · intro c h; cases h; exact h0
  · intro l x ih c h
    obtain ⟨c1, xx, h1, hst⟩ := grun_snoc_inv h
    exact hs l c1 x.1 x.2 c xx h1 (ih c1 h1) hst

/-- The `Write1Reply` a replica sends for operation `o` with its store's tag `t`. -/
def w1rep (o : Op) (t : model.Tag) : Msg := .write1Reply ⟨o.rid, o.cid, ⟨-1, t⟩⟩

theorem proj_take_len_mono (l : List Label) (r : Fin 3) {a b : Nat} (hab : a ≤ b) :
    (projR (l.take a) r).length ≤ (projR (l.take b) r).length := by
  have : l.take b = l.take a ++ (l.drop a).take (b - a) := by
    rw [← List.take_add]; congr 1; omega
  rw [this, proj_append, List.length_append]; omega

theorem cutSt_take {l : List Label} {k n : Nat} (hk : k ≤ n) (r : Fin 3) :
    cutSt (l.take n) k r = cutSt l k r := by
  unfold cutSt; rw [List.take_take, Nat.min_eq_left hk]

end Perennial.gryff.pure
