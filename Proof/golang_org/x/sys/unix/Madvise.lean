/-
The proof of `Spec/golang_org/x/sys/unix/Madvise.lean`: an arbitrary errno.
-/
module

public import Spec.golang_org.x.sys.unix.Madvise
public import GooseLang.Ext.Fs.Madvise

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [golang_org.x.sys.unix.Assumptions]

theorem golang_org.x.sys.unix.Madvise.wp_proof : golang_org.x.sys.unix.Madvise.spec (GF := GF) (hG := hG) := by
  intro sl advice hadv hlen
  wp_start as #Hinv
  have h : uint.Z advice ≤ uint.Z (W64 3) := by
    simp only [uint.Z]; have : (W64 3).toNat = 3 := rfl; omega
  rw [decide_eq_true h]
  wp_auto
  by_cases hl0 : sl.len = W64 0
  · rw [decide_eq_true hl0]
    wp_auto
    wp_apply wp_ArbitraryInt as %x _
    iapply wp_errno
    iapply HΦ
    iempintro
  · rw [decide_eq_false hl0]
    wp_auto
    by_cases h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len
    · rw [if_pos h0]
      wp_auto
      wp_apply wp_osMadvise _ _ advice hadv CoPset.subseteq_top $$ Hinv
      iintro %e
      iapply wp_errno
      iapply HΦ
      iempintro
    · exfalso; apply h0
      have : sl.len.toInt ≠ 0 := fun h => hl0 (BitVec.eq_of_toInt_eq (by simpa using h))
      simp only [sint.Z]; exact ⟨by decide, by have := hlen; simp at *; omega⟩

end proof

end EtcdGrove
end Perennial
