/-
The proof of `SetCodec` (`Spec/encoding/json/Codec/SetCodec.lean`): under `codecMu`, the
invariant's half of `codec` and the caller's `codecUnset` make the whole points-to, at `nil` (so no
panic); after the store, one half goes back to the invariant and the other is kept for good
(`codecSetWith`; as net/rpc's `SetCodec`).
-/
module

public import Spec.encoding.json.Codec.SetCodec
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace encoding.json

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions] [sync.Assumptions]

theorem SetCodec.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    SetCodec.spec (GF := GF) (hG := hG) := by
  intro fm fu c
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
  wp_apply wp_Unlock (globalAddr encoding.json.codecMu)
      iprop(∃ c : Loc, typedPointsto (globalAddr encoding.json.codec) c (DFrac.own (1 : Qp).half))
      $$ [$Hpkg $Hmu $Hown Hh1]
  · iexists c; iexact Hh1
  iapply HΦ
  unfold codecSetWith codecInv
  iframe Hpkg Hmu
  iexists c
  iframe Hkeep Hc
  ipureintro; exact Hcnn

end proof

end encoding.json
end Perennial
