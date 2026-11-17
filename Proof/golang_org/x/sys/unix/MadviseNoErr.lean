/-
The proof of `Spec/golang_org/x/sys/unix/MadviseNoErr.lean`: `wp_osMadviseNE` (a mapping has a
cell, so the zero-length branch is not taken).
-/
module

public import Spec.golang_org.x.sys.unix.MadviseNoErr
public import Proof.golang_org.x.sys.unix.Madvise
public import Perennial.Golang.Theory.Unsafe

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

theorem golang_org.x.sys.unix.Madvise.wp_proofNoErr :
    golang_org.x.sys.unix.Madvise.specNoErr (GF := GF) (hG := hG) := by
  intro Sio _ hS base len cap advice p dq m n hadv hbase hpos hb
  wp_start as ⟨#Hinv, Hm⟩
  have h : uint.Z advice ≤ uint.Z (W64 3) := by
    simp only [uint.Z]; have : (W64 3).toNat = 3 := rfl; omega
  rw [decide_eq_true h]
  wp_auto
  have hl0 : len ≠ W64 0 := by rintro rfl; exact absurd hpos (by decide)
  rw [decide_eq_false hl0]
  wp_auto
  have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z len := by
    simp only [sint.Z]; exact ⟨by decide, hpos⟩
  rw [if_pos h0]
  rw [show sint.Z (W64 0) = 0 from rfl, sliceIndexRef_byte ⟨base, len, cap⟩ 0 hbase (Int.le_refl _)]
  have hb0 : (base +ₗ (0 : Int)) = base := by simp
  rw [hb0]
  wp_auto
  wp_apply wp_osMadviseNE hS base len advice p dq m n hadv hb CoPset.subseteq_top
    $$ Hinv Hm as Hm
  iapply wp_errno
  iapply HΦ
  iexact Hm

end proof

end EtcdGrove
end Perennial
