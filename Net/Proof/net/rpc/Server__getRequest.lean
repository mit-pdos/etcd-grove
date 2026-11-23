/-
The proof of `Server.getRequest` (`Net/Spec/net/rpc/Server__getRequest.lean`): `reqLock`, then the
head of the free list (zeroed) or a new `Request`.
-/
module

public import Net.Spec.net.rpc.Server__getRequest
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

theorem Server.getRequest.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    Server.getRequest.spec (GF := GF) (hG := hG) := by
  intro s γ
  wp_start as #Hs
  unfold isServer
  icases Hs with ⟨#Hsync, #Hmu, #Hrq, #Hrs⟩
  wp_auto
  wp_apply wp_Lock _ _ $$ [$Hsync $Hrq] as ⟨Hown, Hinv⟩
  iunfold reqFreeInv at Hinv
  icases Hinv with ⟨%fr, %rs, Hfr, Hch⟩
  wp_auto
  cases rs with
  | nil =>
    iunfold reqChain at Hch
    icases Hch with %Hnull
    subst Hnull
    wp_auto
    wp_apply wp_Unlock _ (reqFreeInv s) $$ [$Hsync $Hrq $Hown Hfr]
    · iunfold reqFreeInv
      iexists null, []
      iframe Hfr
      iunfold reqChain
      ipureintro; rfl
    (try wp_auto)
    iapply HΦ
    iexact «$r0»
  | cons r rs =>
    iunfold reqChain at Hch
    icases Hch with ⟨%Hr, %v, Hv, Hch⟩
    subst Hr
    ihave %Hnn := typedPointsto_not_null $$ Hv
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_Unlock _ (reqFreeInv s) $$ [$Hsync $Hrq $Hown Hfr Hch]
    · iunfold reqFreeInv
      iexists v.next', rs
      iframe Hfr Hch
    (try wp_auto)
    iapply HΦ
    iexact Hv

end proof

end net.rpc
end Perennial
