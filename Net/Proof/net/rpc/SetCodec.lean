/-
The proof of `SetCodec` (`Net/Spec/net/rpc/SetCodec.lean`): under `codecMu`, the invariant's half
of `codec` and the caller's `codecUnset` make the whole points-to, at `nil` (so no panic); after
the store, one half goes back to the invariant and the other is kept for good (`codecSet`).
-/
module

public import Net.Spec.net.rpc.SetCodec
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

theorem SetCodec.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    SetCodec.spec (GF := GF) (hG := hG) := by
  intro C c
  wp_start as ⟨#Hmu, Hunset, #Hc, %Hcnn⟩
  wp_auto
  wp_apply wp_Lock _ _ $$ [$Hpkg $Hmu] as ⟨Hown, Hinv⟩
  unfold codecInv codecUnset
  icases Hinv with ⟨%c0, Hhalf⟩
  icases typedPointsto_half_combine _ _ _ 1 $$ [$Hhalf $Hunset] with ⟨%Heq, Hfull⟩
  subst Heq
  wp_auto
  icases (typedPointsto_half_split _ c 1).1 $$ Hfull with ⟨Hh1, Hh2⟩
  imod (typedPointsto_dfractional (GF := GF) _ c).dfractional_persist _ $$ Hh2 with #Hkeep
  wp_apply wp_Unlock (globalAddr net.rpc.codecMu)
      iprop(∃ c : Loc, typedPointsto (globalAddr net.rpc.codec) c (DFrac.own (1 : Qp).half))
      $$ [$Hpkg $Hmu $Hown Hh1]
  · iexists c; iexact Hh1
  iapply HΦ
  unfold codecSet codecInv
  iframe Hpkg Hmu
  iexists c
  iframe Hkeep Hc
  ipureintro; exact Hcnn

end proof

end net.rpc
end Perennial
