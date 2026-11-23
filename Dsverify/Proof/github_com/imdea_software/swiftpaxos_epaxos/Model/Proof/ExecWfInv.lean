/-
(p-exec, MODEL-REQUEST exec-M1) What a scan pass of the executor needs of a replica's state
(`ExecWf`, `Epaxos/Proof/epaxos/ExecModel.lean`), from the invariant: `execWf_of_inv`.

Derived from existing conjuncts, except `ExecedUpTo[q] ≥ -1` (`InvAux.execLo`, new):
* ids, deps, `ExecedUpTo`'s upper bound: `Inv.wf` (an executed instance is in range);
* committed non-NONE commands are the run's client commands (`OpCmdOk`): `Inv.agreement` (a committed record holds a
  committed value) + `Inv.slots` (a committed value is a no-op or its owner's batch, whose
  proposals are client ops) + the ops' premise `OpsOk` (what `epInv` knows of the ops: `cmdOf` of
  an input meeting `kit.pre`; a pure premise here, the model does not constrain `clientPropose`);
* a held batch covers the non-NONE commands: `Inv.wf` (a held batch is the owner) + `Inv.slots`;
* stored values only at keys `< 2`, below `2^15`: `Inv.execPrefix` (the store is the last PUT of
  the executed sequence, whose slots are in the global sequence; a PUT touches only its key) +
  `Inv.clientOps` (a global slot's command is its op's) + `Inv.slots` + `OpsOk`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ExecModel

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

/-- The ops' commands are the run's client commands (`OpCmdOk`: the ops are `cmdOf` of inputs
meeting the run's premise: `epInv`'s ops list, `opsPre`; stage 2, review T1-3). -/
def OpsOk (S : Sys) : Prop := ∀ o ∈ S.ops, OpCmdOk o.2.cmd

namespace ExecWfProof

theorem lastPut_mem_foldl (s : List (Slot × WCmd)) (v0 : Option (List w8)) (val : List w8)
    (h : s.foldl (fun v e => if e.2.op = opPUT then some e.2.val else v) v0 = some val) :
    v0 = some val ∨ ∃ e ∈ s, e.2.op = opPUT ∧ e.2.val = val := by
  induction s generalizing v0 with
  | nil => exact Or.inl h
  | cons e s ih =>
    simp only [List.foldl_cons] at h
    rcases ih _ h with h' | ⟨e', he', h1, h2⟩
    · by_cases hp : e.2.op = opPUT
      · simp only [hp, ite_true] at h'
        exact Or.inr ⟨e, by simp, hp, Option.some.inj h'⟩
      · simp only [hp, ite_false] at h'; exact Or.inl h'
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h1, h2⟩

theorem lastPut_mem {s : List (Slot × WCmd)} {val : List w8} (h : Sys.lastPut s = some val) :
    ∃ e ∈ s, e.2.op = opPUT ∧ e.2.val = val := by
  rcases lastPut_mem_foldl s none val h with h | h
  · cases h
  · exact h

end ExecWfProof

open ExecWfProof in
/-- **The executor's facts from the invariant** (and the ops' premise). -/
theorem execWf_of_inv (S : Sys) (hS : Inv S) (hops : OpsOk S) (i : Nat) (hi : i < nR) :
    ExecWf (S.rep i) := by
  obtain ⟨hwf, -, -, -, -, -, -, -, -, -, -, hagr, -, -, -, -, -, -, -, -, hpre, hslots, hcops,
    -⟩ := hS.1
  obtain ⟨-, hwf2, -, -, hexUp, -⟩ := hwf
  -- a non-NONE slot's command is a client op's
  have hcmd : ∀ x v c, S.committedVal x v → c ∈ v.cmds → c.op ≠ opNONE → OpCmdOk c := by
    intro x v c hv hc hn
    rcases hslots.1 x v hv with h | ⟨ps, hps, h⟩
    · rw [h] at hc; simp only [noop, List.mem_singleton] at hc; subst hc
      exact absurd rfl hn
    · rw [h] at hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      exact hops _ (hslots.2 x ps hps p hp)
  refine ⟨fun x w h => ?_, fun x w h hs => ?_, hexUp i hi, fun q hq => ?_,
    fun x w hw hc c hc' hn => ?_, fun x w lb ps hw hc hlb hps idx c hidx hne => ?_,
    fun k v hk => ?_⟩
  · obtain ⟨-, h1, h2, -⟩ := hwf2 i hi x w h; exact ⟨h1, h2⟩
  · obtain ⟨-, -, -, h3, -⟩ := hwf2 i hi x w h; exact h3 hs
  · -- `ExecedUpTo[q]`: at least `-1` (`execLo`); if nonnegative, an executed (in range) index
    refine ⟨hS.2.execLo i hi q hq, ?_⟩
    by_cases h0 : 0 ≤ zz ((S.rep i).execedUpTo q)
    · have hn : ((toN ((S.rep i).execedUpTo q) : Nat) : Int) ≤ zz ((S.rep i).execedUpTo q) := by
        simp only [toN, zz] at h0 ⊢; omega
      obtain ⟨w, hw, -⟩ := hexUp i hi q hq _ hn
      obtain ⟨-, -, hlt, -⟩ := hwf2 i hi _ w hw
      simp only [toN, zz] at hlt h0 ⊢; omega
    · have : zz ((S.rep i).execedUpTo q) = -1 := by
        have := hS.2.execLo i hi q hq; omega
      rw [this]; simp [MAX_INSTANCE]
  · -- committed commands
    obtain ⟨-, hv⟩ := hagr.2 i hi x w hw hc
    exact hcmd x _ c hv hc' hn
  · -- a held batch is the owner's, which the committed value is (or a no-op)
    obtain ⟨-, -, -, -, -, -, hown⟩ := hwf2 i hi x w hw
    have ho := hown lb ps hlb hps
    obtain ⟨-, hv⟩ := hagr.2 i hi x w hw hc
    rcases hslots.1 x _ hv with h | ⟨ps', hps', h⟩
    · exfalso
      simp only [instVal] at h
      rw [h] at hidx
      cases idx with
      | zero => simp only [noop, List.getElem?_cons_zero, Option.some.injEq] at hidx
                subst hidx; exact hne rfl
      | succ n => simp [noop] at hidx
    · rw [ho] at hps'; cases hps'
      simp only [instVal] at h
      rw [h] at hidx
      have := (List.getElem?_eq_some_iff.mp hidx).1
      simpa using this
  · -- the store: the last PUT of the executed sequence, a global slot's op's value (and key)
    rw [hpre.2.1 i hi k] at hk
    obtain ⟨e, he, hput, hval⟩ := lastPut_mem hk
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem he
    obtain ⟨gpre, gpost, hg, -⟩ := hpre.2.2 i hi k pre e post hsplit
    have hge : e ∈ S.gexec k := by rw [hg]; simp
    obtain ⟨htk, -, -, ⟨p, hp, hpc⟩, -⟩ := hcops.2.2.2.1 k e hge
    have hkey : e.2.key = k := by
      rcases htk with h | ⟨h, -⟩
      · exact h
      · rw [hput] at h; exact absurd h (by decide)
    unfold Sys.slotOp at hp
    cases ho : S.owner e.1.1 with
    | none => rw [ho] at hp; cases hp
    | some ps =>
      rw [ho] at hp
      have hok := hops _ (hslots.2 e.1.1 ps ho p (List.mem_of_getElem? hp))
      simp only at hok
      rw [hpc] at hok
      obtain ⟨hk2, hcase⟩ := hok
      refine ⟨hkey ▸ hk2, ?_⟩
      rw [← hval]
      rcases hcase with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩
      · rw [hput] at h; exact absurd h (by decide)
      · exact h
      · rw [hput] at h; exact absurd h (by decide)

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
