/-
The proof of `Dec.Str` (`Spec/.../dist/enc/Dec__Str.lean`): `U64` of the length; a failed read or fewer bytes
left than the length clear the flag; otherwise the string is the next bytes (`ownSlice_slice`,
`wp_bytes_to_string`) and the rest is kept.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Str
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__U64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Assumptions]

theorem Dec.Str.wp_proof (wp_U64 : Dec.U64.spec (GF := GF) (hG := hG)) :
    Dec.Str.spec (GF := GF) (hG := hG) := by
  intro d bs ok
  wp_start as Hd
  wp_auto
  wp_apply wp_U64 d bs ok $$ [Hd] as %n Hd
  · iframe
  unfold decPost
  icases Hd with (⟨%r, %Hr, Hd⟩ | ⟨%r, Hd⟩)
  · unfold ownDec
    icases Hd with ⟨%s, %dq, Hd, Hs⟩
    ihave %Hl := ownSlice_len _ _ _ $$ Hs
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
    try wp_auto
    by_cases hn : uint.Z s.len < uint.Z n
    · rw [show decide (uint.Z s.len < uint.Z n) = true from decide_eq_true hn]
      wp_auto
      iapply HΦ
      iright
      iexists r, s, dq
      iframe
    · rw [show decide (uint.Z s.len < uint.Z n) = false from decide_eq_false hn]
      wp_auto
      have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z n ∧ sint.Z n ≤ sint.Z s.len := by
        word
      rw [ite_eq_left ⟨hb.1, hb.2.1, Int.le_trans hb.2.2 Hwf.2⟩]
      icases (ownSlice_slice (W64 0) n s dq r hb).1 $$ Hs with ⟨-, Hmid, Hrest⟩
      wp_apply wp_bytes_to_string _ _ dq $$ Hmid as Hmid
      rw [ite_eq_left ⟨hb.2.1, hb.2.2, Hwf.2⟩]
      try wp_auto
      have hk : sint.nat n ≤ r.length := by
        have : sint.nat s.len = (sint.Z s.len).toNat := rfl
        have : sint.nat n = (sint.Z n).toNat := rfl
        omega
      have hsub : subslice 0 (sint.nat n) r = r.take (sint.nat n) := by
        simp [subslice]
      have hW : (W64 (r.take (sint.nat n)).length : w64) = n := by
        rw [List.length_take, Nat.min_eq_left hk]
        have : sint.nat n = (sint.Z n).toNat := rfl
        word
      rw [hsub]
      iapply HΦ
      ileft
      iexists r.drop (sint.nat n)
      isplitr
      · ipureintro
        refine ⟨Hr.1, ?_⟩
        rw [Hr.2, encStr, hW, List.append_assoc, List.take_append_drop]
      iexists slice.slice s w8 n s.len, dq
      iframe
  · unfold ownDec
    icases Hd with ⟨%s, %dq, Hd, Hs⟩
    try wp_auto
    iapply HΦ
    iright
    iexists r, s, dq
    iframe

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
end Perennial
