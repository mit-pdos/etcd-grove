/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/WitRun.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AW, internal: **the witness invariant along a run**, and the witness of a committed copy at
any cut (`witness_cut`: the exact content of unit L's `witness_committed`,
`GryffProof/PureL/Witness.lean`, which calls it; `Op`/`rmwInst` are unfolded there).

`wit_reach`: every prefix of a run from the initial configuration has histories `G` (agreement)
and `S` (witnesses) with `CInv`, `WInv`, and `Link`: each RMW label `n` of replica `r` recorded, at
the instance `(r, crt[r] at the cut n)` it created, the stores of the cut `n`. It takes the stores'
growth per step (`TagMono`: unit L's `step_tag_mono`, `PureL/StoreSteps.lean`, which `PureA` cannot
import) as a hypothesis.
-/
module

public import Dsverify.Proof.gryff.PureA.WitStep
public import Dsverify.Proof.gryff.PureL.Run

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AW

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA

/-- A step never lowers the store (unit L's `step_tag_mono`). -/
def TagMono : Prop :=
  ∀ (r : Fin 3) (s s' : RState) (e : Ev) (o : List Out), stepR r s e = .ok (s', o) → TLe s.tag s'.tag

theorem tag_mono_step (hT : TagMono) {c c1 : Cfg gNet} {a : Fin 3} {e : Ev} {x : List Ext}
    (h : GStep c a e c1 x) (w : Fin 3) : TLe (c.st w).tag (c1.st w).tag := by
  obtain ⟨s', o, hs, -, -, hst, hinf⟩ := h
  have hp : Post c a e s' o c1 := ⟨hst, hinf⟩
  by_cases hw : w = a
  · subst hw; rw [st_postA hp]; exact hT _ _ _ _ _ (gstep_ok hs)
  · rw [st_postN hp hw]; exact TLe.refl _

/-- Each RMW label recorded the stores of its cut at its instance. -/
def Link (l : List Label) (S : CSG) : Prop :=
  ∀ n (r : Fin 3) rid cid (k : w64) (d : Dep) (oldV newV : w64),
    l[n]? = some (r, .rmw rid cid k d oldV newV) →
    S (rid32 r) ((cutSt l n r).crt (rid32 r)) = some (fun w => (cutSt l n w).tag)

theorem cutSt_append {l l' : List Label} {n : Nat} (hn : n ≤ l.length) (r : Fin 3) :
    cutSt (l ++ l') n r = cutSt l n r := by
  unfold cutSt; rw [List.take_append_of_le_length hn]

theorem cutSt_len {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r : Fin 3) :
    cutSt l l.length r = c.st r := by
  unfold cutSt; rw [List.take_length]
  obtain ⟨o, ho⟩ := kahn.grun_state h r
  exact stOf_of_runP ho

theorem cutSt_take {l : List Label} {n g : Nat} (hg : g ≤ n) (r : Fin 3) :
    cutSt (l.take n) g r = cutSt l g r := by
  unfold cutSt; rw [List.take_take, Nat.min_eq_left hg]

/-- **The invariants along a run.** -/
theorem wit_reach (hT : TagMono) {l : List Label} :
    ∀ {c : Cfg gNet}, GRun (Cfg.init gNet) l c → ∃ G S, CInv c G ∧ WInv c S ∧ Link l S := by
  induction l using snoc_ind with
  | h0 =>
    intro c h; cases h
    exact ⟨_, _, inv_init, wit_init, fun n _ _ _ _ _ _ _ h => by simp at h⟩
  | hs l x ih =>
    intro c h
    obtain ⟨c', h1, h2⟩ := pure.grun_append h
    obtain ⟨c1, xx, hs, hr⟩ := grun_cons_inv h2
    cases hr
    obtain ⟨G, S, I, W, L⟩ := ih h1
    obtain ⟨G1, I1, -⟩ := inv_step I hs
    refine ⟨G1, newS c' x.1 x.2 S, I1, wit_step I I1 W hs (tag_mono_step hT hs), ?_⟩
    intro n r rid cid k d oldV newV hn
    by_cases hlt : n < l.length
    · rw [List.getElem?_append_left hlt] at hn
      have e : (fun w => (cutSt (l ++ [x]) n w).tag) = (fun w => (cutSt l n w).tag) :=
        funext fun w => by rw [cutSt_append (Nat.le_of_lt hlt)]
      rw [e, cutSt_append (Nat.le_of_lt hlt)]
      exact newS_le W _ _ _ _ _ (L n r rid cid k d oldV newV hn)
    · have hge : l.length ≤ n := Nat.le_of_not_lt hlt
      rw [List.getElem?_append_right hge] at hn
      have hn0 : n - l.length = 0 := by
        cases hm : n - l.length with
        | zero => rfl
        | succ j => rw [hm] at hn; simp at hn
      have en : n = l.length := by omega
      subst en
      rw [hn0] at hn
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      have e : (fun w => (cutSt (l ++ [(r, Ev.rmw rid cid k d oldV newV)]) l.length w).tag) =
          (fun w => (c'.st w).tag) := funext fun w => by rw [cutSt_append (Nat.le_refl _), cutSt_len h1]
      rw [e, cutSt_append (Nat.le_refl _), cutSt_len h1]
      exact if_pos ⟨rfl, rfl⟩

/-! ## The owner's `crt` grows along a run -/

theorem runP_own {r : Fin 3} {es : List Ev} {s : RState} {o : List Out}
    (h : runP gNet r es = some (s, o)) {j k : Nat} (hjk : j ≤ k) (hk : k ≤ es.length) :
    (stOf r (es.take k)).id = (stOf r (es.take j)).id ∧
      sint.Z ((stOf r (es.take j)).crt (stOf r (es.take j)).id) ≤
        sint.Z ((stOf r (es.take k)).crt (stOf r (es.take j)).id) := by
  induction k with
  | zero =>
    have : j = 0 := by omega
    subst this; exact ⟨rfl, Int.le_refl _⟩
  | succ k ih =>
    by_cases e : j = k + 1
    · subst e; exact ⟨rfl, Int.le_refl _⟩
    have hk' : k < es.length := by omega
    obtain ⟨o', hs⟩ := runP_step h (List.getElem?_eq_getElem hk')
    obtain ⟨s1, o1, h1⟩ := runP_take h k
    have hL : Loc (stOf r (es.take k)) := by
      have := runP_loc h1; rwa [← stOf_of_runP h1] at this
    have L := (step_lk hL hs).1
    obtain ⟨i1, i2⟩ := ih (by omega) (by omega)
    refine ⟨L.1.trans i1, ?_⟩
    have k3 := L.2.2.1
    rw [i1] at k3
    exact Int.le_trans i2 k3

theorem stOf_nil_id (r : Fin 3) : (stOf r []).id = rid32 r := by
  have e : stOf r [] = RState.init r.val := stOf_of_runP (runP_nil r)
  rw [e]; rfl

theorem projR_take_prefix (l : List Label) (n : Nat) (r : Fin 3) :
    projR (l.take n) r = (projR l r).take (projR (l.take n) r).length := by
  have e := pure.proj_append (l.take n) (l.drop n) r
  rw [List.take_append_drop] at e
  rw [e]
  exact (List.take_left' rfl).symm

theorem projR_take_len {l : List Label} {n m : Nat} (h : n ≤ m) (r : Fin 3) :
    (projR (l.take n) r).length ≤ (projR (l.take m) r).length := by
  have e : l.take n = (l.take m).take n := by rw [List.take_take, Nat.min_eq_left h]
  rw [e, projR_take_prefix (l.take m) n r, List.length_take]
  exact Nat.min_le_right _ _

/-- The owner's `crt` of its row only grows along the cuts of a run. -/
theorem cut_crt_mono {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r : Fin 3)
    {n m : Nat} (hnm : n ≤ m) :
    sint.Z ((cutSt l n r).crt (rid32 r)) ≤ sint.Z ((cutSt l m r).crt (rid32 r)) := by
  obtain ⟨o, ho⟩ := kahn.grun_state h r
  have ho' : runP gNet r (projR l r) = some (c.st r, o) := ho
  have ec : ∀ n, cutSt l n r = stOf r ((projR l r).take (projR (l.take n) r).length) := fun n => by
    unfold cutSt; rw [← projR_take_prefix]
  have hlen : ∀ n, (projR (l.take n) r).length ≤ (projR l r).length := fun n => by
    rw [projR_take_prefix l n r, List.length_take]; exact Nat.min_le_right _ _
  have hid : (stOf r ((projR l r).take 0)).id = rid32 r := by rw [List.take_zero]; exact stOf_nil_id r
  obtain ⟨e1, -⟩ := runP_own ho' (Nat.zero_le _) (hlen n)
  obtain ⟨-, k2⟩ := runP_own ho' (projR_take_len hnm r) (hlen m)
  rw [ec n, ec m]
  rw [e1, hid] at k2
  exact k2

/-! ## The witness of a committed copy -/

/-- **The witness of a committed copy at any cut** (unit L's `witness_committed`, with `rmwInst`
unfolded): a committed copy with commands of the instance created by the RMW label `g` of replica
`r0` has a base at least two distinct replicas' stores at the cut `g`. -/
theorem witness_cut (hT : TagMono) {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c)
    {g : Nat} {r0 : Fin 3} {rid cid : w32} {k : w64} {d : Dep} {oldV newV : w64}
    (hg : l[g]? = some (r0, .rmw rid cid k d oldV newV)) {n : Nat} {r : Fin 3} {cp : Copy}
    (hcp : (cutSt l n r).inst (rid32 r0) ((cutSt l g r0).crt (rid32 r0)) = some cp)
    (hst : isCommitted cp.status) (hc : cp.cmds ≠ []) :
    ∃ w1 w2 : Fin 3, w1 ≠ w2 ∧ TLe (cutSt l g w1).tag cp.base.t ∧
      TLe (cutSt l g w2).tag cp.base.t := by
  obtain ⟨cn, hn, -, hst'⟩ := grun_cut h n
  have ecn : ∀ r : Fin 3, cn.st r = cutSt l n r := fun r => by
    obtain ⟨o, ho⟩ := hst' r; exact (stOf_of_runP ho).symm
  obtain ⟨G, S, -, W, L⟩ := wit_reach hT hn
  have hcp' : cpOf cn r (rid32 r0) ((cutSt l g r0).crt (rid32 r0)) = some cp := by
    unfold cpOf; rw [ecn r]; exact hcp
  have hs : Strong cp.status := by
    rcases hst with e | e
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr e))
  obtain ⟨f, hf, k1, -⟩ := (W.copies r _ _ cp hcp').val hc
    (fun e => by rw [e] at hs; exact absurd hs (by unfold Strong; decide))
  by_cases hgn : g < n
  · have hg' : (l.take n)[g]? = some (r0, .rmw rid cid k d oldV newV) := by
      rw [List.getElem?_take_of_lt hgn]; exact hg
    have hL : S (rid32 r0) ((cutSt (l.take n) g r0).crt (rid32 r0)) =
        some (fun w => (cutSt (l.take n) g w).tag) := L g r0 rid cid k d oldV newV hg'
    rw [cutSt_take (Nat.le_of_lt hgn) r0, hf] at hL
    have ef : ∀ w : Fin 3, f w = (cutSt l g w).tag := fun w => by
      have := congrFun (Option.some.inj hL) w
      rw [this, cutSt_take (Nat.le_of_lt hgn)]
    obtain ⟨w1, w2, hne, h1, h2⟩ := k1 hs
    refine ⟨w1, w2, hne, ?_, ?_⟩
    · have := h1; unfold W1 at this; rwa [ef] at this
    · have := h2; unfold W1 at this; rwa [ef] at this
  · exfalso
    obtain ⟨r', hr', hlt⟩ := W.born _ _ _ hf
    have := rid32_inj hr'; subst this
    rw [ecn r0] at hlt
    have := cut_crt_mono h r0 (Nat.le_of_not_lt hgn)
    omega

end Perennial.gryff.pureA.AW
