/-
The proof of `Spec/os/File__ReadAt.lean`: the model's loop, by Löb induction over its `EINTR`
retries, with `b` holding anything of its length; a successful `pread` reads every byte, so the
loop then ends at once.
-/
module

public import Spec.os.File__ReadAt

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
variable [os.Assumptions]

theorem os.File.ReadAt.wp_proof : os.File.ReadAt.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf sl vs off dq dqm dqb d m xs hrd hoff hn2 hin hxl
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hsl, Hosfd, Hm, Hbs⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  icases ownSlice_len sl _ vs $$ Hsl with %Hlen
  wp_auto
  have h0 : ¬ (sint.Z off < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hoff
  rw [decide_eq_false h0]
  wp_auto
  icases ownSlice_wf sl _ vs $$ Hsl with %Hwf
  have hslz : sint.Z sl.len = vs.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  clear Hlen
  obtain ⟨cur, hcur⟩ : ∃ cur, cur = vs := ⟨_, rfl⟩
  ihave Hsl := (show sl ↦* vs ⊢ sl ↦* cur by rw [hcur]) $$ Hsl
  have hcl : cur.length = vs.length := by rw [hcur]
  clear hcur
  iloeb as IH generalizing %cur %hcl Hsl Hosfd Hm Hbs Hfd HΦ
  by_cases hl0 : sl.len = W64 0
  · rw [decide_eq_true hl0]
    wp_auto
    have hv0 : vs.length = 0 := by
      rw [hl0, show sint.Z (W64 0) = 0 from rfl] at hslz; omega
    iapply HΦ
    iframe
    isplitl []
    · isplitl [] <;> iassumption
    ipureintro
    refine ⟨hcl, .inl ⟨by rw [hv0]; rfl, rfl, ?_⟩⟩
    rw [List.length_eq_zero_iff.1 (hcl.trans hv0), List.length_eq_zero_iff.1 (hxl.trans hv0)]; rfl
  · rw [decide_eq_false hl0]
    wp_auto
    have hmx : ¬ (sint.Z (W64 1073741824) < sint.Z sl.len) := by
      rw [hslz, show sint.Z (W64 1073741824) = 1073741824 from rfl]; omega
    rw [decide_eq_false hmx]
    wp_auto
    wp_apply wp_osPRead fd off sl.len dq dqm dqb d m xs CoPset.subseteq_top hrd hoff
      (by simp only [sint.Z] at hslz; have := BitVec.toInt_eq_toNat_cond sl.len; split at this <;> omega)
      $$ Hinv Hosfd Hm Hbs as %r %e %hre Hosfd Hm Hbs
    have hrl : r.length ≤ vs.length := by
      rcases hre with ⟨-, rfl⟩ | ⟨-, k, hk, rfl⟩
      · simp [hxl]
      · simp; omega
    wp_apply wp_string_to_bytes r as %tmp ⟨Htmp, -⟩
    wp_apply wp_slice_copy sl cur tmp r (DFrac.own 1) $$ [Hsl Htmp] as %mm ⟨%hmm, Hsl, -⟩
    · iframe
    have hvl : (r.take cur.length ++ cur.drop r.length).length = vs.length := by simp; omega
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      rw [decide_eq_false hl0]
      iapply IH $$ %_ %hvl Hsl Hosfd Hm Hbs Hfd HΦ
    · rw [decide_eq_false he4]
      wp_auto
      rcases hre with ⟨rfl, rfl⟩ | ⟨he0, -⟩
      · rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
        simp only [Bool.not_true]
        have hrl' : (xs.map Prod.fst).length = vs.length := by simp [hxl]
        have hmmv : sint.nat mm = vs.length := by rw [hmm, hcl, hrl']; omega
        have hmm0 : mm ≠ W64 0 := by
          intro h; rw [h, show sint.nat (W64 0) = 0 from rfl] at hmmv
          simp only [sint.Z] at hslz; rw [← hmmv] at hslz
          exact hl0 (BitVec.eq_of_toInt_eq (by rw [hslz]; rfl))
        wp_auto
        rw [decide_eq_false hmm0]
        wp_auto
        have hmmeq : mm = sl.len := by
          apply BitVec.eq_of_toInt_eq
          simp only [sint.nat, sint.Z] at hmmv hslz
          have : vs.length ≠ 0 := by
            intro h; rw [h] at hslz; exact hl0 (BitVec.eq_of_toInt_eq (by rw [hslz]; rfl))
          omega
        rw [hmmeq, if_pos ⟨Hwf.1, Int.le_refl _, Hwf.2⟩]
        wp_auto
        rw [decide_eq_true (show sl.len - sl.len = W64 0 from BitVec.sub_self sl.len),
          show W64 0 + sl.len = sl.len from BitVec.zero_add _]
        wp_auto
        have hsln : sl.len = W64 vs.length := by
          apply BitVec.eq_of_toInt_eq
          simp only [sint.Z] at hslz
          rw [hslz, W64, BitVec.toInt_ofInt, Int.bmod]; split <;> omega
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          refine ⟨hvl, .inl ⟨hsln, rfl, ?_⟩⟩
          rw [hcl, ← hrl', List.take_length, List.drop_eq_nil_of_le (by rw [hrl', hcl]; exact Nat.le_refl _), List.append_nil]
      · have he0' : ¬ e = W64 0 := he0
        simp only [decide_eq_false he0', Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro; exact ⟨hvl, .inr ⟨rfl, by intro h; cases h⟩⟩


theorem os.File.ReadAt.wp_proofRacy : os.File.ReadAt.specRacy (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
