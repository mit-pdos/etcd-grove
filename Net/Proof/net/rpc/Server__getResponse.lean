/-
The proof of `Server.getResponse` (`Net/Spec/net/rpc/Server__getResponse.lean`): `respLock`, then the
head of the free list (zeroed) or a new `Response`.
-/
module

public import Net.Spec.net.rpc.Server__getResponse
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [sync.Assumptions]

theorem Server.getResponse.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    Server.getResponse.spec (GF := GF) (hG := hG) := by
  intro s γ
  wp_start as #Hs
  unfold isServer
  icases Hs with ⟨#Hsync, #Hmu, #Hrq, #Hrs⟩
  wp_auto
  wp_apply wp_Lock _ _ $$ [$Hsync $Hrs] as ⟨Hown, Hinv⟩
  iunfold respFreeInv at Hinv
  icases Hinv with ⟨%fr, %rs, Hfr, Hch⟩
  wp_auto
  cases rs with
  | nil =>
    iunfold respChain at Hch
    icases Hch with %Hnull
    subst Hnull
    wp_auto
    wp_apply wp_Unlock _ (respFreeInv s) $$ [$Hsync $Hrs $Hown Hfr]
    · iunfold respFreeInv
      iexists null, []
      iframe Hfr
      iunfold respChain
      ipureintro; rfl
    (try wp_auto)
    iapply HΦ
    iexact «$r0»
  | cons r rs =>
    iunfold respChain at Hch
    icases Hch with ⟨%Hr, %v, Hv, Hch⟩
    subst Hr
    ihave %Hnn := typedPointsto_not_null $$ Hv
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_Unlock _ (respFreeInv s) $$ [$Hsync $Hrs $Hown Hfr Hch]
    · iunfold respFreeInv
      iexists v.next', rs
      iframe Hfr Hch
    (try wp_auto)
    iapply HΦ
    iexact Hv

end proof

end net.rpc
end Perennial
