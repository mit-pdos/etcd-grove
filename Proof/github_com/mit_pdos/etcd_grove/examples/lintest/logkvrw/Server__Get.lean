/-
Lean-first (no Rocq counterpart).

The proof of `(*Server).Get`: the linearization point is right after `s.mu.Lock()`: the lock
invariant's half of the register's ghost variable agrees with the caller's (`regState`), and
`s.state` is its value, which the critical section reads and returns.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Server__Get
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvrw

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Assumptions]

theorem Server.Get.wp_proof : Server.Get.spec (GF := GF) (hG := hG) := by
  intro γ s
  iintro %Φ ⟨#Hpkg, #Hs⟩ HAU
  iunfold isServer at Hs
  icases Hs with ⟨%γr, %c, #Hc, #Hcond, #Hmu⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply sync.Mutex.wp_Lock (muAddr s) (logkvrwR γ γr s) $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold logkvrwR at HR
  icases HR with ⟨%sl, %rs, %a, %st, Hlog, Hsl, Hcap, Happ, Hst, Hg, Hrs, %Ha, Hdone, Hpend⟩
  wp_auto
  -- the linearization point
  simp only [LawfulSet.diff_empty]
  iapply fupd_wp
  imod HAU with ⟨%x, Hx, Hclose⟩
  iunfold regState at Hx
  icombine Hg Hx gives %Hagree
  obtain ⟨_, Heq⟩ := Hagree
  subst Heq
  imod Hclose $$ [Hx] with HΦ
  · iunfold regState; iexact Hx
  imodintro
  wp_apply sync.Mutex.wp_Unlock (muAddr s) (logkvrwR γ γr s)
    $$ [$Hmu $Hlocked Hlog Hsl Hcap Happ Hst Hg Hrs Hdone Hpend]
  · iunfold logkvrwR
    iexists sl, rs, a, st
    iframe
    ipureintro; exact Ha
  iapply HΦ
  itrivial

end proof

end logkvrw
end lintest
end EtcdGrove
end Perennial
