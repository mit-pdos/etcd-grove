/-
Lean-first (no Rocq counterpart).

The proof of `(*Server).Get`: the linearization point is right after `s.mu.Lock()`: the lock
invariant's half of the register's ghost variable agrees with the caller's (`regState`), and
the snapshot `s.snap` points to holds its value; the snapshot is read-only (`↦□`), so reading it
after `Unlock` still gives that value.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvsnap.Server__Get
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvsnap

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvsnap.Assumptions]

theorem Server.Get.wp_proof : Server.Get.spec (GF := GF) (hG := hG) := by
  intro γ s
  iintro %Φ ⟨#Hpkg, #Hs⟩ HAU
  iunfold isServer at Hs
  icases Hs with ⟨%γr, %c, #Hc, #Hcond, #Hmu⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply sync.Mutex.wp_Lock (muAddr s) (logkvsnapR γ γr s) $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold logkvsnapR at HR
  icases HR with ⟨%sl, %rs, %a, %st, %p, Hlog, Hsl, Hcap, Hsnap, #Hp, Hg, Hrs, %Ha, Hdone, Hpend⟩
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
  wp_apply sync.Mutex.wp_Unlock (muAddr s) (logkvsnapR γ γr s)
    $$ [$Hmu $Hlocked Hlog Hsl Hcap Hsnap Hg Hrs Hdone Hpend]
  · iunfold logkvsnapR
    iexists sl, rs, a, st, p
    iframe
    iframe #
    ipureintro; exact Ha
  iStructNamed Hp
  wp_auto
  iapply HΦ
  itrivial

end proof

end logkvsnap
end lintest
end EtcdGrove
end Perennial
