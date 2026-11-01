/-
The proofs of `Spec/os/CrashSt.lean`: the models' loops as in `Proof/os/Crash.lean`,
`Proof/os/File__Truncate.lean`, `Proof/os/File__Sync.lean` and `Proof/golang_org/x/sys/unix/*.lean`,
over the steps of `Proof/os/CrashStOps.lean`. A write's loop keeps a state it reached (`WReach`),
a truncate's one of the three `TReach` states. Lean-first (no Rocq counterpart).
-/
module

public import Spec.os.CrashSt
public import Proof.golang_org.x.sys.unix.Munmap
public import Perennial.Golang.Theory.Plain

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

theorem syscall.Fdatasync.wp_proof_crashS [syscall.Assumptions] :
    syscall.Fdatasync.specCrashS (GF := GF) (hG := hG) := by
  intro fd dq d N γ Ok m H F T fa fb hd hH hF hc hN hok hokF
  wp_start as ⟨#Hos, #Hinv, Hfd, Hown⟩
  wp_apply wp_osFsync_cs fd dq d N γ Ok m H F T fa fb hH hF hd hc hN hok hokF $$ Hos Hinv Hfd Hown
    as %e Hr Hfd
  iapply wp_errno
  iapply HΦ
  iframe Hfd
  icases Hr with (⟨%he, H⟩ | ⟨%he, H⟩)
  · ileft; iframe; ipureintro; exact he
  · iright; iframe; ipureintro; exact he.1

theorem golang_org.x.sys.unix.Mmap.wp_proof_crashS [golang_org.x.sys.unix.Assumptions] :
    golang_org.x.sys.unix.Mmap.specCrashS (GF := GF) (hG := hG) := by
  intro fd off len prot fl dq d N γ Ok m bs fa fb hrd hoff hlen hprot hfl hN hok
  wp_start as ⟨#Hos, #Hinv, Hfd, Hown⟩
  have hl : ¬ (sint.Z len ≤ sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; simp only [sint.Z]; omega
  rw [decide_eq_false hl]
  wp_auto
  wp_apply wp_osMmap_cs fd off len prot fl dq d N γ Ok m bs fa fb hN hrd hoff hlen hprot hfl hok
    $$ Hos Hinv Hfd Hown as %base %e Hr Hfd
  icases Hr with (⟨%he, Hown, Hc⟩ | ⟨%he, Hown⟩)
  · obtain ⟨rfl, hpos, hmax⟩ := he
    rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
    simp only [Bool.not_true]
    wp_auto
    wp_func_call
    wp_call
    have hnn : base ≠ null := by intro h; subst h; simp [null] at hpos
    have hlz : sint.Z len = (len.toNat : Int) := by
      simp only [sint.Z]; have := BitVec.toInt_eq_toNat_cond len; split at this <;> omega
    rw [ite_eq_right (by omega), ite_eq_right hnn,
      ite_eq_right (by simp only [maxAddr] at hmax; push_cast; omega)]
    wp_auto
    rw [← show errnoErr 0 = interface.nil by unfold errnoErr; rfl]
    iapply HΦ
    iframe
    ileft
    iexists base
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
  · obtain ⟨he, rfl⟩ := he
    have he' : ¬ e = W64 0 := he
    simp only [decide_eq_false he', Bool.not_false]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    iframe
    iright
    iframe
    ipureintro; exact ⟨he, rfl⟩

theorem golang_org.x.sys.unix.Munmap.wp_proof_crashS [golang_org.x.sys.unix.Assumptions] :
    golang_org.x.sys.unix.Munmap.specCrashS (GF := GF) (hG := hG) := by
  intro base len p N γ Ok m bs fa fb vf hpos hb hN hok
  wp_start as ⟨#Hos, #Hinv, Hown, Hc⟩
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
    wp_apply wp_osMunmap_cs base len len p N γ Ok m bs fa fb len.toNat vf hN hb rfl rfl hok
      $$ Hos Hinv Hown Hc as %e Hr
    iapply wp_errno
    iapply HΦ
    iexact Hr

variable [os.Assumptions]

theorem os.File.Sync.wp_proof_crashS : os.File.Sync.specCrashS (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d N γ Ok m H F T fa fb hd hH hF hc hN hok hokF
  unfold os.ownFile
  wp_start as ⟨#Hos, #Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hown⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  wp_apply wp_osFsync_cs fd dq d N γ Ok m H F T fa fb hH hF hd hc hN hok hokF
    $$ Hos Hinv Hosfd Hown as %e Hr Hosfd
  by_cases he4 : e = W64 4
  · icases Hr with (⟨%he, -⟩ | ⟨%he, -⟩)
    · exact absurd (he4 ▸ he) (by decide)
    · exact absurd he4 he.2
  rw [decide_eq_false he4]
  wp_auto
  icases Hr with (⟨%he, Hown⟩ | ⟨%he, Hown⟩)
  · subst he
    rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
    simp only [Bool.not_true]
    wp_auto
    iapply HΦ
    iframe
    isplitl []
    · isplitl [] <;> iassumption
    ileft
    isplitr; · ipureintro; rfl
    iframe
  · have he0' : ¬ e = W64 0 := he.1
    simp only [decide_eq_false he0', Bool.not_false]
    wp_auto
    wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
    iapply HΦ
    iframe
    isplitl []
    · isplitl [] <;> iassumption
    iright
    iframe
    ipureintro; intro h; cases h

theorem os.OpenFile.wp_proof_crashS [os.file.FieldAssumptions] :
    os.OpenFile.specCrashS (GF := GF) (hG := hG) := by
  intro path perm N γ Ok s hs hN hok
  wp_start as ⟨#Hos, #Hinv, Hown⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = s := ⟨_, rfl⟩
  ihave Hown := (show csOwn path γ s ⊢ csOwn path γ s' by rw [hs']) $$ Hown
  have hm2 : s' = s ∨ s' = csOpen s := .inl hs'
  clear hs'
  iloeb as IH generalizing %s' %hm2 Hown HΦ
  rw [os.file_ty_eq, os.File_ty_eq,
    show (W64 66 ||| W64 524288) = W64 0x80042 from by decide]
  have hs2 : s' = none ∨ ∃ m bs fa fb, s' = some ⟨m, bs, fa, fb, .idle⟩ := by
    rcases hm2 with rfl | rfl
    · exact hs
    · rcases hs with rfl | ⟨m, bs, fa, fb, rfl⟩
      · exact .inr ⟨_, _, _, _, rfl⟩
      · exact .inr ⟨_, _, _, _, rfl⟩
  have hos : csOpen s' = csOpen s := by
    rcases hm2 with rfl | rfl
    · rfl
    · rcases hs with rfl | ⟨m, bs, fa, fb, rfl⟩ <;> rfl
  wp_apply wp_osOpen_cs path (W64 0x80042) N γ Ok s' hs2 hN
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
    have hm3 : s2 = s ∨ s2 = csOpen s := by
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

end proof

end EtcdGrove
end Perennial
