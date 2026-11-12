/-
The proof of `Spec/golang_org/x/sys/unix/Madvise.lean`: an arbitrary errno.
-/
module

public import Spec.golang_org.x.sys.unix.Madvise

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [golang_org.x.sys.unix.Assumptions]

theorem golang_org.x.sys.unix.Madvise.wp_proof : golang_org.x.sys.unix.Madvise.spec (GF := GF) (hG := hG) := by
  intro sl advice hadv
  wp_start
  have h : uint.Z advice ≤ uint.Z (W64 3) := by
    simp only [uint.Z]; have : (W64 3).toNat = 3 := rfl; omega
  rw [decide_eq_true h]
  wp_auto
  wp_apply wp_ArbitraryInt as %x _
  iapply wp_errno
  iapply HΦ
  iempintro

end proof

end EtcdGrove
end Perennial
