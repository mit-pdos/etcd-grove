/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/TryLockFile.lean`:
`ofdTryLockFile`'s and `flockTryLockFile`'s (`wp_ofdTryLockFile`, `wp_flockTryLockFile`), then
`TryLockFile`'s, over the package fact's lock function. As `LockFile.lean`, with the lock error's
`errors.Is(err, EWOULDBLOCK)` (`errors.IsErrno.spec`, a hypothesis) and the errors' `errOk`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TryLockFile
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.LockFile
public import LinuxFs.Spec.errors.IsErrno
public import LinuxFs.Proof.syscall.ErrorOk

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
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- A `fmtErrorOk` error is `errOk`. -/
theorem fileutil.errOk_of_fmtErrorOk (e : GoInterfaceOk) :
    fmtErrorOk (GF := GF) (GoInterface.ok e) ⊢ errOk e := by
  unfold fmtErrorOk
  iintro ⟨-, H⟩
  unfold errOk
  rw [fmt.stringMethodSpec_unfold]
  iexact H

/-- The try-lock's errors: an errno's, replaced by `ErrLocked` when `errors.Is` says so. -/
theorem fileutil.errnoErr_errOk (e : w64) (he : e ≠ 0) :
    ⊢ (∃ ii : GoInterfaceOk, ⌜errnoErr e = GoInterface.ok ii⌝ ∗ errOk (GF := GF) ii) := by
  have h := errnoErr_fmtErrorOk (GF := GF) e he
  have hne : errnoErr e = interface.mkOk syscall.Errno.ty #e := by
    unfold errnoErr; simp only [he, ↓reduceIte]
  rw [hne] at h ⊢
  iintro
  iexists _
  isplitr
  · ipureintro; rfl
  iapply fileutil.errOk_of_fmtErrorOk
  iapply h

theorem fileutil.wp_ofdTryLockFile
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG))
    (wp_IsErrno : errors.IsErrno.spec (GF := GF) (hG := hG))
    (path : GoString) (flag : w64) (perm : w32) (P : IProp GF) (X : Type)
    (A : X → Bool → IProp GF) (C : X → Ino → Prop)
    (hopen : fileutil.OpenTriple P path flag perm A C) :
    {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
        P }}
      (App (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.ofdTryLockFile)) (Val #path))
        (Val #flag)) (Val #perm))
    {{ (lf : Loc) (err : GoInterface), RET (PairV #lf #err);
        fileutil.lockPost A C path flag lf err ∗
        (⌜err = interface.nil⌝ ∨ ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ errOk e) }} := by
  wp_start as ⟨#Hinv, #Hpkg, HP⟩
  ihave #Hdef := fileutil.pkgInit_fact $$ Hpkg
  icases Hdef with ⟨-, ⟨%w, #Hw, %hw⟩, %eL, #HeL, #HeLok⟩
  wp_auto
  unfold fileutil.OpenTriple at hopen
  wp_apply hopen $$ HP as %f %err Hr
  unfold fileutil.openPost
  icases Hr with ⟨%x, (⟨%he, HA, %fd, %i, %hfi, Hf, Hoff, Hfd⟩ | ⟨%he, HA, #Herr⟩)⟩
  rotate_left
  · obtain ⟨he, rfl⟩ := he
    cases err with
    | nil => exact absurd rfl he
    | ok ie =>
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_Errorf _ _ [interface.mkOk go.string #path, GoInterface.ok ie] [ie] (by
          intro ii hii
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hii
          rcases hii with h | h
          · rw [interface.mkOk] at h; cases h; exact Or.inl (argWf_string _)
          · cases h; exact Or.inr (by simp)) $$ [Hsl2] as %err2 #Herr2
    · iframe
      iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
      iapply fileutil.errOk_of_fmtErrorOk
      unfold fmtErrorOkOrNil
      iexact Herr
    iapply HΦ
    isplitl [HA]
    · unfold fileutil.lockPost
      iexists x
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
      iexists false
      iexact HA
    iright
    iexists err2
    iframe Herr2
    ipureintro; rfl
  subst he
  wp_auto
  wp_apply wp_Fd f fd path (DFrac.own 1) $$ Hf as Hf
  wp_apply syscall.FcntlFlock.wp_lock fd (W64 37) flock_ptr (DFrac.own 1) _ (.inr (.inr (.inl rfl)))
    $$ [Hinv Hfd] as %e Hfd
  · iframe; iexact Hinv
  by_cases he : e = 0
  · subst he
    have h0 : errnoErr (0 : w64) = interface.nil := by unfold errnoErr; simp
    rw [h0]
    iapply wp_fupd
    wp_auto
    ipersist «$r0»
    imodintro
    iapply HΦ
    isplitl [HA Hf Hoff Hfd]
    · unfold fileutil.lockPost
      iexists x
      ileft
      isplitr
      · ipureintro; rfl
      iframe HA
      iexists f, fd, i
      iframe Hf Hoff Hfd
      isplitr
      · ipureintro; exact hfi
      unfold fileutil.lockedFile
      iexact «$r0»
    ileft
    ipureintro; rfl
  · ihave #Hek := fileutil.errnoErr_errOk (GF := GF) e he
    icases Hek with ⟨%ek, %hek, #Hek⟩
    have hne : errnoErr e = interface.mkOk syscall.Errno.ty #e := by unfold errnoErr; simp only [he, ↓reduceIte]
    rw [hne] at hek ⊢
    wp_auto
    wp_apply wp_Close f fd path _ $$ [Hinv Hf Hfd] as %cerr ⟨Hf, -⟩
    · iframe; iexact Hinv
    rw [← hne]
    wp_apply wp_IsErrno e (W64 11) he $$ [] as %b _
    · iPkgInit
    cases b
    · wp_auto
      iapply HΦ
      isplitl [HA]
      · unfold fileutil.lockPost
        iexists x
        iright
        isplitr
        · ipureintro; exact ⟨(fun h => by rw [hne] at h; cases h), rfl⟩
        iexists true
        iexact HA
      iright
      iexists ek
      iframe Hek
      ipureintro; exact hne ▸ hek
    · wp_auto
      iapply HΦ
      isplitl [HA]
      · unfold fileutil.lockPost
        iexists x
        iright
        isplitr
        · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
        iexists true
        iexact HA
      iright
      iexists eL
      iframe HeLok
      ipureintro; rfl

theorem fileutil.wp_flockTryLockFile
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_Flock : syscall.Flock.spec (GF := GF) (hG := hG))
    (wp_IsErrno : errors.IsErrno.spec (GF := GF) (hG := hG))
    (path : GoString) (flag : w64) (perm : w32) (P : IProp GF) (X : Type)
    (A : X → Bool → IProp GF) (C : X → Ino → Prop)
    (hopen : fileutil.OpenTriple P path flag perm A C) :
    {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
        P }}
      (App (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.flockTryLockFile)) (Val #path))
        (Val #flag)) (Val #perm))
    {{ (lf : Loc) (err : GoInterface), RET (PairV #lf #err);
        fileutil.lockPost A C path flag lf err ∗
        (⌜err = interface.nil⌝ ∨ ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ errOk e) }} := by
  wp_start as ⟨#Hinv, #Hpkg, HP⟩
  ihave #Hdef := fileutil.pkgInit_fact $$ Hpkg
  icases Hdef with ⟨-, ⟨%w, #Hw, %hw⟩, %eL, #HeL, #HeLok⟩
  wp_auto
  unfold fileutil.OpenTriple at hopen
  wp_apply hopen $$ HP as %f %err Hr
  unfold fileutil.openPost
  icases Hr with ⟨%x, (⟨%he, HA, %fd, %i, %hfi, Hf, Hoff, Hfd⟩ | ⟨%he, HA, #Herr⟩)⟩
  rotate_left
  · obtain ⟨he, rfl⟩ := he
    cases err with
    | nil => exact absurd rfl he
    | ok ie =>
    wp_auto
    iapply HΦ
    isplitl [HA]
    · unfold fileutil.lockPost
      iexists x
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
      iexists false
      iexact HA
    iright
    iexists ie
    isplitr
    · ipureintro; rfl
    iapply fileutil.errOk_of_fmtErrorOk
    unfold fmtErrorOkOrNil
    iexact Herr
  subst he
  wp_auto
  wp_apply wp_Fd f fd path (DFrac.own 1) $$ Hf as Hf
  wp_apply wp_Flock $$ [Hinv Hfd] as %e Hfd
  · iframe; iexact Hinv
  by_cases he : e = 0
  · subst he
    have h0 : errnoErr (0 : w64) = interface.nil := by unfold errnoErr; simp
    rw [h0]
    iapply wp_fupd
    wp_auto
    ipersist «$r0»
    imodintro
    iapply HΦ
    isplitl [HA Hf Hoff Hfd]
    · unfold fileutil.lockPost
      iexists x
      ileft
      isplitr
      · ipureintro; rfl
      iframe HA
      iexists f, fd, i
      iframe Hf Hoff Hfd
      isplitr
      · ipureintro; exact hfi
      unfold fileutil.lockedFile
      iexact «$r0»
    ileft
    ipureintro; rfl
  · ihave #Hek := fileutil.errnoErr_errOk (GF := GF) e he
    icases Hek with ⟨%ek, %hek, #Hek⟩
    have hne : errnoErr e = interface.mkOk syscall.Errno.ty #e := by unfold errnoErr; simp only [he, ↓reduceIte]
    rw [hne] at hek ⊢
    wp_auto
    wp_apply wp_Close f fd path _ $$ [Hinv Hf Hfd] as %cerr ⟨Hf, -⟩
    · iframe; iexact Hinv
    rw [← hne]
    wp_apply wp_IsErrno e (W64 11) he $$ [] as %b _
    · iPkgInit
    cases b
    · wp_auto
      iapply HΦ
      isplitl [HA]
      · unfold fileutil.lockPost
        iexists x
        iright
        isplitr
        · ipureintro; exact ⟨(fun h => by rw [hne] at h; cases h), rfl⟩
        iexists true
        iexact HA
      iright
      iexists ek
      iframe Hek
      ipureintro; exact hne ▸ hek
    · wp_auto
      iapply HΦ
      isplitl [HA]
      · unfold fileutil.lockPost
        iexists x
        iright
        isplitr
        · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
        iexists true
        iexact HA
      iright
      iexists eL
      iframe HeLok
      ipureintro; rfl

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.TryLockFile.wp_proof
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_Flock : syscall.Flock.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG))
    (wp_IsErrno : errors.IsErrno.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.TryLockFile.spec (GF := GF) (hG := hG) := by
  intro path flag perm P X A C hopen
  wp_start as ⟨#Hinv, #Hpkg, HP⟩
  ihave #Hdef := fileutil.pkgInit_fact $$ Hpkg
  icases Hdef with ⟨⟨%ofd, -, #Hlk⟩, -, -⟩
  wp_auto
  cases ofd
  · simp only [fileutil.tryLockFn, Bool.false_eq_true, ↓reduceIte]
    wp_apply fileutil.wp_flockTryLockFile wp_Fd wp_Close wp_Flock wp_IsErrno path flag perm P X A C
      hopen $$ [HP] as %lf %err H
    · iframe; isplitl [] <;> iassumption
    iapply HΦ $$ H
  · simp only [fileutil.tryLockFn, ↓reduceIte]
    wp_apply fileutil.wp_ofdTryLockFile wp_Fd wp_Close wp_Errorf wp_IsErrno path flag perm P X A C
      hopen $$ [HP] as %lf %err H
    · iframe; isplitl [] <;> iassumption
    iapply HΦ $$ H

end proof

end EtcdGrove
end Perennial
