/-
`PcKeep` (I3b, `wal-tc12`): an `OsMeta` keeps knowing the candidates of every byte past both sizes that
another knew (`OsMeta.pc`), as a resize's outcome whose `tc` knows at least `rsTail`'s domain does
(`TcKnows`, `TcKnowsF`): the fact `fileutil`'s split growths carry (`preGrownH`) for `ZeroToEnd`'s
post (`ZteMeta`), from which the WAL's tail gets `TailZ` back. Pure; untrusted.
-/
module

public import LinuxFs.Proof.os.TcKnows

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- **`m'` knows the candidates of every byte past both sizes `m` knew.** -/
def PcKeep (m m' : OsMeta) : Prop :=
  ∀ b, m.size ≤ b → m'.size ≤ b → (m.pc b).isSome → (m'.pc b).isSome

theorem PcKeep.refl (m : OsMeta) : PcKeep m m := fun _ _ _ h => h

/-- Through a middle state no longer than one of the ends. -/
theorem PcKeep.trans {m m1 m2 : OsMeta} (h1 : PcKeep m m1) (h2 : PcKeep m1 m2)
    (hs : m1.size ≤ max m.size m2.size) : PcKeep m m2 :=
  fun b hb hb2 hp => h2 b (by omega) hb2 (h1 b hb (by omega) hp)

/-- `PcKeep` does not depend on the resize stamps. -/
theorem PcKeep.withTc_self {m m' : OsMeta} (h : PcKeep m m') (rz : List Nat) :
    PcKeep m (m'.withTc m'.tc rz) := h

theorem OsMeta.pc_isSome_of_tc {M : OsMeta} {b : Nat} (h : (M.tc !! b).isSome) : (M.pc b).isSome := by
  unfold OsMeta.pc
  cases hc : M.tc !! b with
  | none => rw [hc] at h; cases h
  | some c => rfl

/-- **A resize's outcome keeps `m`'s known candidates**: an `OsMeta` of the size `sz'` the resize of `m`
to `tg` left, with the announcement's known zeros, whose `tc` knows at least what `rsTail` knows (the
outcomes of `os.ftDoneH`/`os.ftUndoneH`, `TcKnows`, and of `fallocOutH`, `TcKnowsF`). -/
theorem PcKeep.of_tc {tr : Bool} {m M : OsMeta} {tg sz' : Nat} (hsz : M.size = sz')
    (hzf : M.zf = (m.announce (min m.size tg) (rsHi tr m.size tg) tg).zf)
    (htc : ∀ b, (rsTail tr m tg sz' 0 [] !! b).isSome → (M.tc !! b).isSome) : PcKeep m M := by
  intro b hb hb' hp
  by_cases hin : min m.size tg ≤ b ∧ b < rsHi tr m.size tg ∧ sz' ≤ b
  · apply OsMeta.pc_isSome_of_tc; apply htc
    rw [rsTail_lookup, if_pos hin, if_neg (by omega)]
    cases hc : m.pc b with
    | none => rw [hc] at hp; cases hp
    | some c => rfl
  · have hhi : rsHi tr m.size tg ≤ b := by omega
    have hr : inRange (min m.size tg) (rsHi tr m.size tg) b = false := by
      simp only [inRange, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    unfold OsMeta.pc at hp
    cases hmc : m.tc !! b with
    | some c =>
      apply OsMeta.pc_isSome_of_tc; apply htc
      rw [rsTail_lookup, if_neg hin, announce_tc, hr, hmc]; rfl
    | none =>
      rw [hmc] at hp
      cases hz : m.zf with
      | none => rw [hz] at hp; cases hp
      | some z =>
        rw [hz] at hp
        have hzb : z ≤ b := if h : z ≤ b then h else by simp [h] at hp
        unfold OsMeta.pc
        cases hMc : M.tc !! b with
        | some c => rfl
        | none =>
          simp only [hzf, announce_zf, hz, Option.map_some]
          rw [if_pos (by split <;> omega)]; rfl

end Fs
end Perennial

end
