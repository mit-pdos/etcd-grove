/-
The proof of `CounterApply.spec` (`(*Counter).Apply` with a plain update and no thread token):
lintest's proof (`Proof/.../lintest/counter/Counter__Apply.lean`): the linearization point is right
after `c.mu.Lock()`, where the lock invariant's half of the ghost variable agrees with the state.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.CounterApply
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

open EtcdGrove.lintest.counter

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter.Assumptions]

theorem CounterApply.wp_proof : CounterApply.spec (GF := GF) (hG := hG) := by
  intro γ c b Φ
  wp_start as Hpre
  icases Hpre with ⟨#Hc, HAU⟩
  wp_auto
  iunfold isCounter at Hc
  wp_apply sync.Mutex.wp_Lock (muAddr c) (counterR γ c) $$ [$Hc] as ⟨Hlocked, %n, Hn, Hg⟩
  iapply fupd_wp
  imod HAU with ⟨%s, Hs, Hcommit⟩
  icombine Hg Hs gives % ⟨_, Heq⟩
  subst Heq
  imod ghostVar_update_halves (counterNext n (boxB b)) γ _ _ $$ Hg Hs with ⟨Hg, Hs⟩
  imod Hcommit $$ Hs with HR
  imodintro
  rw [counterNext_boxB]
  cases b <;> (simp only [Bool.false_eq_true, ite_false, ite_true]; wp_auto)
  all_goals
    wp_apply sync.Mutex.wp_Unlock (muAddr c) (counterR γ c) $$ [$Hc $Hlocked Hn Hg]
    · iexists _
      iframe
    iapply HΦ
    iexists _
    iframe HR
    ipureintro; rfl

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
