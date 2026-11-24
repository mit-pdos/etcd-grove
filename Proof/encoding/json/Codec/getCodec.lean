/-
The proof of `getCodec` (`Spec/encoding/json/Codec/getCodec.lean`): under `codecMu`, the invariant's
half of `codec` agrees with the registered codec kept for good; it is not `nil`, so no panic (as
net/rpc's `getCodec`).
-/
module

public import Spec.encoding.json.Codec.getCodec
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

theorem getCodec.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    getCodec.spec (GF := GF) (hG := hG) := by
  intro fm fu
  wp_start as #Hset
  unfold codecSetWith
  icases Hset with ⟨#Hsync, #Hmu, %c, %Hcnn, #Hcodec, #Hc⟩
  wp_auto
  wp_apply wp_Lock _ _ $$ [$Hsync $Hmu] as ⟨Hown, Hinv⟩
  unfold codecInv
  icases Hinv with ⟨%c', Hhalf⟩
  icombine Hhalf Hcodec gives %Heq
  subst Heq
  wp_apply wp_Unlock (globalAddr encoding.json.codecMu)
      iprop(∃ c : Loc, typedPointsto (globalAddr encoding.json.codec) c (DFrac.own (1 : Qp).half))
      $$ [$Hsync $Hmu $Hown Hhalf]
  · iexists c'; iexact Hhalf
  rw [decide_eq_false Hcnn]
  wp_auto
  iapply HΦ $$ Hc

end proof

end encoding.json
end Perennial
