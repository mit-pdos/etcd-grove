/-
The proof of `Server.freeResponse` (`Net/Spec/net/rpc/Server__freeResponse.lean`): `respLock`, then
the `Response` pushed on the free list.
-/
module

public import Net.Spec.net.rpc.Server__freeResponse
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
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS] [sync.Assumptions]

theorem Server.freeResponse.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    Server.freeResponse.spec (GF := GF) (hG := hG) := by
  intro s γ req v
  wp_start as ⟨#Hs, Hv⟩
  unfold isServer
  icases Hs with ⟨#Hsync, #Hmu, #Hrq, #Hrs⟩
  wp_auto
  wp_apply wp_Lock _ _ $$ [$Hsync $Hrs] as ⟨Hown, Hinv⟩
  iunfold respFreeInv at Hinv
  icases Hinv with ⟨%fr, %rs, Hfr, Hch⟩
  wp_auto
  wp_apply wp_Unlock _ (respFreeInv s) $$ [$Hsync $Hrs $Hown Hfr Hch Hv]
  · iunfold respFreeInv
    iexists req, req :: rs
    iframe Hfr
    iunfold respChain
    isplitr
    · ipureintro; rfl
    iexists { v with next' := fr }
    iframe Hv Hch
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end net.rpc
end Perennial
