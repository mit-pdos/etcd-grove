module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.uidOf

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem uidOf.wp_proof :
    uidOf.spec (GF := GF) (hG := hG) := by
  intro u
  wp_start as -
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %s1 ⟨Hs1, -⟩
  wp_apply wp_bytes_to_string $$ [$Hs1] as Hs1
  (try wp_auto)
  have h : [W8 (uint.Z (u >>> W64 8)), zero_val w8].set (sint.nat (W64 (0 + 1))) (W8 (uint.Z u)) =
      uidOfL u := by
    have e : sint.nat (W64 (0 + 1)) = 1 := by decide
    rw [e]
    simp only [List.set, uidOfL, List.cons.injEq, and_true]
    constructor
    · apply BitVec.eq_of_toNat_eq
      simp [W8, uint.Z, BitVec.extractLsb', BitVec.toNat_ushiftRight]
      simp only [Int.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      omega
    · apply BitVec.eq_of_toNat_eq
      simp [W8, uint.Z, BitVec.extractLsb']
  rw [h]
  iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
