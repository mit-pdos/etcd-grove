/- Lean-first (no Rocq counterpart). Proof of `Spec/github_com/anishathalye/porcupine/byTime__Len.lean`. -/
module

public import Spec.github_com.anishathalye.porcupine.byTime__Len

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem byTime.Len.wp_proof : byTime.Len.spec (GF := GF) (hG := hG) :=
  fun sl es dq => by
  wp_start as Hs
  wp_auto
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have : sl.len = W64 (es.length : Int) := by
    rw [Hl.1]
    show sl.len = BitVec.ofInt 64 ((sint.Z sl.len).toNat : Int)
    rw [Int.toNat_of_nonneg Hl.2]
    exact BitVec.ofInt_toInt.symm
  rw [this]
  iapply HΦ
  iexact Hs

end proof

end porcupine
end EtcdGrove
end Perennial
