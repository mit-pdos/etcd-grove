/-
The proofs of `Spec/os/Crash.lean`: the models' loops as in `Proof/os/OpenFile.lean`,
`Proof/os/File__WriteAt.lean` and `Proof/syscall/Fdatasync.lean`, over the crash-aware steps of
`Proof/os/CrashOps.lean`. A write's loop keeps a narrowing of the file it started from
(`narrow_fin`), whose crashes the first attempt's cover (`crashOk_narrow`).
-/
module

public import Spec.os.Crash

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

theorem syscall.Fdatasync.wp_proof_crash [syscall.Assumptions] :
    syscall.Fdatasync.specCrash (GF := GF) (hG := hG) := by
  intro fd dq d N γ Good m bs hN hok
  wp_start as ⟨#Hos, #Hinv, Hfd, Hown⟩
  wp_apply wp_osFsync_cf fd dq d N γ Good m bs hN hok $$ Hos Hinv Hfd Hown as %e Hr Hfd
  iapply wp_errno
  iapply HΦ
  iframe Hfd
  icases Hr with (⟨%he, H⟩ | ⟨%he, H⟩)
  · ileft; iframe; ipureintro; exact he
  · iright; iframe; ipureintro; exact he.1

variable [os.Assumptions]

theorem os.OpenFile.wp_proof_crash [os.file.FieldAssumptions] :
    os.OpenFile.specCrash (GF := GF) (hG := hG) := by
  intro path perm N γ Good s hs hN hok
  wp_start as ⟨#Hos, #Hinv, Hown⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = s := ⟨_, rfl⟩
  ihave Hown := (show cfOwn path γ s ⊢ cfOwn path γ s' by rw [hs']) $$ Hown
  have hm2 : s' = s ∨ s' = openState s := .inl hs'
  clear hs'
  iloeb as IH generalizing %s' %hm2 Hown HΦ
  rw [os.file_ty_eq, os.File_ty_eq,
    show (W64 66 ||| W64 524288) = W64 0x80042 from by decide]
  have hs2 : s' = none ∨ ∃ m bs, s' = some (m, bs, none) := by
    rcases hm2 with rfl | rfl
    · exact hs
    · rcases hs with rfl | ⟨m, bs, rfl⟩
      · exact .inr ⟨_, _, rfl⟩
      · exact .inr ⟨_, _, rfl⟩
  have hos : openState s' = openState s := by
    rcases hm2 with rfl | rfl
    · rfl
    · rcases hs with rfl | ⟨m, bs, rfl⟩ <;> rfl
  wp_apply wp_osOpen_cf path (W64 0x80042) N γ Good s' hs2 hN
    (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) (by decide)
    (by rw [hos]; exact hok) $$ Hos Hinv Hown as %fd %e %s2 %hres Hown Hfd
  have hfd : openFd path (W64 0x80042) = ⟨path, true, true⟩ := by
    simp [openFd, O_WRONLY, O_RDONLY]
  by_cases he0 : e = W64 0
  · subst he0
    rw [decide_eq_true rfl]
    ihave Hfd := (show (if W64 0 = (0 : w64) then osFd (GF := GF) fd (DFrac.own 1)
        (openFd path (W64 524354)) else emp) ⊢ osFd fd (DFrac.own 1) ⟨path, true, true⟩
      by rw [hfd]; split
         · iintro H; iexact H
         · exact absurd rfl ‹_›) $$ Hfd
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    obtain ⟨-, hfd0, hs2e⟩ := hres.resolve_right (fun h => h.1 rfl)
    rw [hos] at hs2e
    subst hs2e
    iapply HΦ
    ileft
    iexists fd
    iframe
    isplitr
    · ipureintro; exact ⟨rfl, hfd0⟩
    unfold os.ownFile
    iexists inner_ptr
    iframe
    isplitl [] <;> iassumption
  · rw [decide_eq_false he0]
    iclear Hfd
    have hm3 : s2 = s ∨ s2 = openState s := by
      rcases hres with ⟨h, -⟩ | ⟨-, -, h | h⟩
      · exact absurd h he0
      · rw [h]; exact hm2
      · rw [h, hos]; exact .inr rfl
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      try rw [show (W64 66 ||| W64 524288) = W64 0x80042 from by decide]
      iapply IH $$ %_ %hm3 Hown HΦ
    · rw [decide_eq_false he4]
      wp_auto
      unfold os.model.pathError
      wp_apply wp_errno
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
      iexists s2
      iframe
      ipureintro; exact hm3

theorem cfOwn_wf' (p : GoString) (γ : GName) (s : CFile) :
    cfOwn (GF := GF) p γ s ⊢ ⌜CfWf s⌝ := by
  unfold cfOwn; iintro ⟨-, -, %h⟩; ipureintro; exact h

theorem os.File.WriteAt.wp_proof_crash : os.File.WriteAt.specCrash (GF := GF) (hG := hG) := by
  intro f fd name dqf sl data dqs off dq d N γ Good m bs hwr hoff hn hn2 hN hW
  unfold os.ownFile
  wp_start as ⟨#Hos, #Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hsl, Hosfd, Hown⟩
  icases cfOwn_wf' _ _ _ $$ Hown with %Hwf
  have hlen : bs.length = m.size := Hwf.1
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  icases ownSlice_len sl dqs data $$ Hsl with %Hlen
  icases ownSlice_wf sl dqs data $$ Hsl with %Hwfs
  wp_auto
  have h0 : ¬ (sint.Z off < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hoff
  rw [decide_eq_false h0]
  wp_auto
  have hl0 : sl.len ≠ W64 0 := by
    intro h; have h1 := Hlen.1; rw [h, show sint.nat (W64 0) = 0 from rfl] at h1; omega
  rw [decide_eq_false hl0]
  wp_pure
  wp_pure
  -- the invariant: a narrowing of the file
  obtain ⟨m', hm'⟩ : ∃ m', m' = m := ⟨_, rfl⟩
  obtain ⟨bs', hbs'⟩ : ∃ bs', bs' = bs := ⟨_, rfl⟩
  have hNar : Narrow m bs off.toNat data m' bs' := by
    subst hm' hbs'; exact narrow_refl _ _ hlen
  ihave Hown := (show cfOwn (GF := GF) d.path γ (some (m, bs, none)) ⊢
    cfOwn d.path γ (some (m', bs', none)) by rw [hm', hbs']) $$ Hown
  clear hm' hbs'
  iloeb as IH generalizing %m' %bs' %hNar Hown Hosfd Hsl Hfd HΦ
  -- one attempt
  wp_auto
  have hslz : sint.Z sl.len = data.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  have hz : sl.len - W64 0 = sl.len := BitVec.sub_zero sl.len
  have hmax : ¬ (sint.Z (W64 1073741824) < sint.Z (sl.len - W64 0)) := by
    rw [hz, hslz, show sint.Z (W64 1073741824) = 1073741824 from rfl]; omega
  rw [decide_eq_false hmax]
  wp_auto
  have hsb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.cap := by
    rw [show sint.Z (W64 0) = 0 from rfl]; omega
  rw [if_pos hsb, ← slice_slice_trivial, show off + W64 0 = off from BitVec.add_zero off]
  wp_apply wp_bytes_to_string sl data dqs $$ Hsl as Hsl
  wp_apply wp_osPWriteStart_cf fd off data dq d N γ Good m' bs' hN hwr hoff
    ((crashOk_narrow hW hlen hNar).2 0) $$ Hos Hinv Hosfd Hown as %t Hosfd Hown
  wp_apply wp_osPWriteFinish_cf t d.path off.toNat data N γ Good m' bs' hN
    (fun k hk => (crashOk_narrow hW hlen (narrow_fin hNar hk)).1) $$ Hos Hinv Hown
    as %k %e %hke Hown
  obtain ⟨hk, hke⟩ := hke
  have hNar' := narrow_fin (k := k) hNar hk
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_pure
    iapply IH $$ %_ %_ %hNar' Hown Hosfd Hsl Hfd HΦ
  · rw [decide_eq_false he4]
    wp_auto
    have hsln : sl.len = W64 data.length := by
      apply BitVec.eq_of_toInt_eq
      simp only [sint.Z] at hslz
      rw [hslz, W64, BitVec.toInt_ofInt, Int.bmod]; split <;> omega
    rcases hke with ⟨rfl, rfl⟩ | he0
    · rw [decide_eq_true (by rw [hsln]; exact BitVec.zero_add _)]
      wp_auto
      iapply HΦ
      iframe
      isplitl []
      · isplitl [] <;> iassumption
      · ipureintro
        refine ⟨hNar', .inl ⟨hsln, rfl, ?_, fun i hi => finBytes_data hNar.len hn i hi⟩⟩
        show off.toNat + data.length ≤ pwSize m'.size off.toNat data.length
        unfold pwSize; split <;> omega
    · have he0' : ¬ e = W64 0 := he0
      by_cases hkl : W64 0 + W64 ↑k = sl.len
      · rw [decide_eq_true hkl]
        wp_auto
        rw [decide_eq_false he0']
        wp_auto
        simp only [decide_eq_false he0', Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨hNar', .inr ⟨rfl, by intro h; cases h⟩⟩
      · rw [decide_eq_false hkl]
        wp_auto
        simp only [decide_eq_false he0', Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨hNar', .inr ⟨rfl, by intro h; cases h⟩⟩

end proof

end EtcdGrove
end Perennial
