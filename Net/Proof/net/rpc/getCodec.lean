/-
The proof of `getCodec` (`Net/Spec/net/rpc/getCodec.lean`): under `codecMu`, the invariant's half
of `codec` agrees with the registered codec kept for good; it is not `nil`, so no panic.
-/
module

public import Net.Spec.net.rpc.getCodec
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [sync.Assumptions]

theorem getCodec.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    getCodec.spec (GF := GF) (hG := hG) := by
  intro C
  wp_start as #Hset
  unfold codecSet
  icases Hset with ⟨#Hsync, #Hmu, %c, %Hcnn, #Hcodec, #Hc⟩
  wp_auto
  wp_apply wp_Lock _ _ $$ [$Hsync $Hmu] as ⟨Hown, Hinv⟩
  unfold codecInv
  icases Hinv with ⟨%c', Hhalf⟩
  icombine Hhalf Hcodec gives %Heq
  subst Heq
  wp_apply wp_Unlock (globalAddr net.rpc.codecMu)
      iprop(∃ c : Loc, typedPointsto (globalAddr net.rpc.codec) c (DFrac.own (1 : Qp).half))
      $$ [$Hsync $Hmu $Hown Hhalf]
  · iexists c'; iexact Hhalf
  rw [decide_eq_false Hcnn]
  wp_auto
  iapply HΦ $$ Hc

end proof

end net.rpc
end Perennial
