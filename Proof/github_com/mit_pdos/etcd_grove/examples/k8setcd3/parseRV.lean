module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.parseRV

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem bytesBE_take_succ (s : GoString) (i : Nat) (b : w8) (h : s[i]? = some b) :
    bytesBE (s.take (i + 1)) = bytesBE (s.take i) <<< 8 ||| b.zeroExtend 64 := by
  have hl : i < s.length := by
    rcases Nat.lt_or_ge i s.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  rw [List.take_succ, h]
  simp [bytesBE, List.foldl_append]

theorem parseRV.wp_proof : parseRV.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8setcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, -, ⟨%eB, #HeB, #HsB⟩, -⟩
  (try wp_auto)
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  wp_if_destruct
  · -- empty: 0
    (try wp_auto)
    iapply HΦ
    have h0 : s.length = 0 := by word
    have : parseRVD s = some 0 := by simp [parseRVD, h0]
    rw [this]
    ipureintro; exact ⟨rfl, rfl⟩
  have Hne0 := Hif
  (try wp_auto)
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_if_destruct
  · have h8 : s.length = 8 := by word
    ihave HI : (∃ (j : w64) (m : w64), "i" ∷ i_ptr ↦ j ∗ "n" ∷ n_ptr ↦ m ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 8 ∧ m = bytesBE (s.take (sint.nat j))⌝ : IProp GF)
        $$ [i n]
    · iexists W64 0, W64 0
      iframe
      ipureintro; exact ⟨by word, by word, rfl⟩
    wp_for HI
    wp_if_destruct
    · have hb : s[sint.nat j]? = some (s.getD (sint.nat j) (W8 0)) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by word)]; rfl
      rw [if_pos Hj.1, hb]
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, bytesBE_take_succ s _ _ hb, ← Hj.2.2]
      have e1 : W64 (uint.Z (s.getD (sint.nat j) (W8 0))) =
          (s.getD (sint.nat j) (W8 0)).zeroExtend 64 := by
        apply BitVec.eq_of_toNat_eq
        have := (s.getD (sint.nat j) (W8 0)).isLt
        simp only [W64, uint.Z, BitVec.toNat_ofInt, BitVec.toNat_setWidth]
        omega
      rw [e1]
      generalize s.getD (sint.nat j) (W8 0) = x
      bv_decide
    · (try wp_auto)
      iapply HΦ
      have hj8 : sint.nat j = 8 := by word
      rw [hj8, ← h8, List.take_length] at Hj
      have : parseRVD s = some (bytesBE s) := by simp [parseRVD, h8]
      rw [this]
      ipureintro; exact ⟨rfl, Hj.2.2⟩
  -- neither empty nor eight bytes: errBadRV
  (try wp_auto)
  iapply HΦ
  have h0 : s.length ≠ 0 := by intro h; apply Hne0; word
  have h8 : s.length ≠ 8 := by intro h; apply Hif; word
  have : parseRVD s = none := by simp [parseRVD, h0, h8]
  rw [this]
  isplitr
  · ipureintro; nofun
  iunfold go_etcd_io.etcd.cache.v3.errStrOk
  imodintro
  iintro %e %he
  cases he
  iexact HsB


end proof

end k8setcd3
end EtcdGrove
end Perennial
