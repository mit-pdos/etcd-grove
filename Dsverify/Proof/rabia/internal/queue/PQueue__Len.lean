/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/queue/PQueue__Len.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/queue.(*PQueue).Len`.
-/
module

public import Dsverify.Proof.rabia.internal.queue.Spec

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.queue

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model rabia.internal.message

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.queue.Assumptions]

theorem PQueue.Len.wp_proof : PQueue.Len.spec (GF := GF) (hG := hG) := fun q xs _sl => by
  wp_start as H
  unfold pqOwn
  icases H with ⟨%sl, %vs, Hq, Hs, Hcap, %Hlen, #Hr⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  have he : sl.len = W64 xs.length := by
    obtain ⟨h1, h2⟩ := Hl; rw [← Hlen, h1]; word
  rw [he]
  iapply HΦ
  iexists sl, vs
  iframe
  iframe Hr; ipureintro; exact Hlen

end proof

end Perennial.rabia.internal.queue
