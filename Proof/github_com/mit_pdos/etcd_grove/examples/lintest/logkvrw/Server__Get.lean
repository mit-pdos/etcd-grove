/-
Lean-first (no Rocq counterpart).

The proof of `(*Server).Get`: the caller's thread token borrows a reader token from the server's
pool for the read lock, and gets it back after. The linearization point is right after
`s.mu.RLock()`: the read lock's share of the lock's half of the register's ghost variable
(`rdR`) agrees with the caller's (`regState`), and `s.state` is its value, which the critical
section reads and returns.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Server__Get
public import Perennial.Proof.sync.Results

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
  iintro %Φ ⟨#Hpkg, #Hs, Htt⟩ HAU
  iunfold isServer at Hs
  icases Hs with ⟨%γr, %γb, %γp, %c, #Hc, #Hcond, #Hw, #Hpool⟩
  -- a reader token, for the thread token
  iapply fupd_wp
  imod threadPool.borrow poolN γp _ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hpool Htt]
    with ⟨Hown, Hloan⟩
  · iframe #; iframe
  imodintro
  wp_method_call
  wp_call
  wp_auto
  wp_apply sync.RWMutex.wp_RLock $$ [$Hown] as ⟨Hrl, HP⟩
  iunfold rdR at HP
  icases HP with ⟨%st, Hst, Hg, Hb⟩
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
  wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl Hst Hg Hb] as Hown
  · iunfold rdR
    iexists st
    iframe
  iapply fupd_wp
  imod threadPool.giveBack poolN γp _ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hpool Hloan Hown]
    with Htt
  · iframe #; iframe
  imodintro
  wp_auto
  iapply HΦ
  iexact Htt

end proof

end logkvrw
end lintest
end EtcdGrove
end Perennial
