/-
The proof of `Spec/golang_org/x/sys/unix/Munmap.lean`: `wp_osMunmap`.
-/
module

public import Spec.golang_org.x.sys.unix.Munmap
public import Perennial.Golang.Theory.Unsafe
public import Proof.golang_org.x.sys.unix.MunmapLemmas

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

theorem golang_org.x.sys.unix.Munmap.wp_proof : golang_org.x.sys.unix.Munmap.spec (GF := GF) (hG := hG) := by
  intro base len p m vf hpos hb
  wp_start as ⟨#Hinv, Hm, Hc⟩
  by_cases hl0 : len = W64 0
  · rw [decide_eq_true hl0]
    wp_auto
    iapply wp_errno
    iapply HΦ
    iright
    isplitr
    · ipureintro; intro h; cases h
    iright; iframe
  · rw [decide_eq_false hl0]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z len := by
      simp only [sint.Z]; exact ⟨by decide, hpos⟩
    rw [if_pos h0]
    have hn : 0 < len.toNat := by
      have := BitVec.toInt_eq_toNat_cond len; split at this <;> omega
    icases cellsR_pos base _ vf hn $$ Hc with ⟨Hc, %hbase⟩
    rw [show sint.Z (W64 0) = 0 from rfl, sliceIndexRef_byte ⟨base, len, len⟩ 0 hbase (Int.le_refl _)]
    have hb0 : (base +ₗ (0 : Int)) = base := by simp
    rw [hb0]
    wp_auto
    wp_apply wp_osMunmap base len len p m len.toNat vf CoPset.subseteq_top hb rfl rfl
      $$ Hinv Hm Hc as %e Hr
    iapply wp_errno
    iapply HΦ
    iexact Hr

end proof

end EtcdGrove
end Perennial
