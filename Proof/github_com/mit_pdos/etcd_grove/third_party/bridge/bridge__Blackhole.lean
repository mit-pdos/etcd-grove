/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/third_party/bridge/bridge__Blackhole.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridge__Blackhole

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridgeP

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.third_party

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.third_party.bridge.Assumptions]

theorem bridge.Blackhole.wp_proof : bridge.Blackhole.spec (GF := GF) (hG := hG) := by
  intro b γ addr
  wp_start as ⟨#Hb, Hown⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isBridge at Hb
  icases Hb with ⟨%l, %sc, %γsc, #Hd, #Hl, #Hrl, #Hsc, #Hscb, #Hmu, #Hwg, #Hwgi, %Htb⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, Hi⟩
  · iframe #
  iunfold lockInv at Hi
  icases Hi with ⟨%m, %conns, %shares, %reg, %pc, %bhc, %γpc, %γbh, %holed, %q, Hconns, Hm, %Hdom,
    Hpausec, #Hpc, Hpcst, Hbh, #Hbhc, Hholed, Hbhst, Hwand, Hregs, Hreg, #Hregf, %Hsub⟩
  iunfold bridgeHoled at Hown
  ihave %Hag := ghostVar_agree γ.holed _ _ _ _ $$ Hown Hholed
  subst Hag
  simp only [Bool.false_eq_true, ↓reduceIte]
  wp_auto
  wp_apply wp_broadcast_chan_close bhc γbh iprop(True) $$ [$Hbhst] as -
  · imodintro; itrivial
  imod ghostVar_update_halves true γ.holed false false $$ Hown Hholed with ⟨Hown, Hholed⟩
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hconns Hm Hpausec Hpcst Hbh Hholed Hwand Hregs Hreg]
  · iframe #
    iunfold lockInv
    iexists m, conns, shares, reg, pc, bhc, γpc, γbh, true, q
    simp only [↓reduceIte]
    iframe
    iframe #
    ipureintro
    exact ⟨Hdom, Hsub⟩
  iapply HΦ
  iunfold bridgeHoled
  iexact Hown

end proof

end bridgeP
end EtcdGrove
end Perennial
