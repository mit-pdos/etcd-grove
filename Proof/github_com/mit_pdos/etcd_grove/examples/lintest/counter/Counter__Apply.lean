/-
Lean-first (no Rocq counterpart).

The proof of `(*Counter).Apply`: the linearization point is right after `c.mu.Lock()`: there the lock invariant gives `c.n = s` (with the ghost variable's other
half, which agrees with the abstract state), and the abstract state goes to
`counterNext s input`, which the critical section then stores in `c.n` and returns. The input
is a boxed `bool` (`counterInOk`), so `input.(bool)` goes through.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Counter__Apply
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace counter

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions]

theorem Counter.Apply.wp_proof :
    Counter.Apply.spec (GF := GF) (hG := hG) := by
  intro γ c
  iintro #Hpkg #Hc
  unfold applySpec
  iintro %i
  imodintro
  iintro %Φ %Hin HAU
  obtain ⟨b, rfl⟩ := Hin
  wp_method_call
  wp_call
  wp_call
  wp_auto
  iunfold isCounter at Hc
  wp_apply sync.Mutex.wp_Lock (muAddr c) (counterR γ c) $$ [$Hc] as ⟨Hlocked, %n, Hn, Hg⟩
  -- the linearization point
  simp only [LawfulSet.diff_empty]
  iapply fupd_wp
  imod HAU with ⟨%s, Hs, Hcommit⟩
  icombine Hg Hs gives % ⟨_, Heq⟩
  subst Heq
  imod ghostVar_update_halves (counterNext n (boxB b)) γ _ _ $$ Hg Hs with ⟨Hg, Hs⟩
  imod Hcommit $$ %(counterNext n (boxB b)) %(boxI (counterNext n (boxB b))) [Hs] with HΦ
  · iframe
    ipureintro
    simp [counterS, counterM_step]
  imodintro
  rw [counterNext_boxB]
  cases b <;> (simp only [Bool.false_eq_true, ite_false, ite_true]; wp_auto)
  all_goals
    wp_apply sync.Mutex.wp_Unlock (muAddr c) (counterR γ c) $$ [$Hc $Hlocked Hn Hg]
    · iexists _
      iframe
    unfold boxI
    iapply HΦ
    simp only [counterS]
    ipureintro
    exact ⟨⟨_, rfl⟩, _, rfl⟩

end proof

end counter
end lintest
end EtcdGrove
end Perennial
