/-
The proof of `Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/LockFile.lean`: `ofdLockFile`'s
and `flockLockFile`'s (`wp_ofdLockFile`, `wp_flockLockFile`), then `LockFile`'s, over the package
fact's lock function.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.LockFile
public import Spec.os.File__Fd
public import Spec.os.File__Close
public import Spec.syscall.Flock
public import Spec.fmt.ErrorfErrs
public import Proof.syscall.FileOps

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

/-- The package fact. -/
theorem fileutil.pkgInit_fact :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ⊢
      fileutil.fileutilInit (GF := GF) :=
  isPkgInit_access (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil

theorem fileutil.wp_ofdLockFile
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG))
    (path : GoString) (flag : w64) (perm : w32) (P : IProp GF) (X : Type)
    (A : X → Bool → IProp GF) (C : X → Ino → Prop)
    (hopen : fileutil.OpenTriple P path flag perm A C)
    (hwr : decide ((flag ||| W64 0x80000).toNat % 4 ≠ O_RDONLY) = true) :
    {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
        fileutil.lockKind (GF := GF) .ofd ∗ P }}
      (App (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.ofdLockFile)) (Val #path))
        (Val #flag)) (Val #perm))
    {{ (lf : Loc) (err : GoInterface), RET (PairV #lf #err); fileutil.lockPost A C path flag lf err }} := by
  wp_start as ⟨#Hinv, #Hpkg, #Hkind, HP⟩
  ihave #Hdef := fileutil.pkgInit_fact $$ Hpkg
  icases Hdef with ⟨-, ⟨%w, #Hw, %hw⟩, -⟩
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
      unfold fmtErrorOkOrNil fmtErrorOk
      icases Herr with ⟨-, H⟩
      unfold errOk
      rw [fmt.stringMethodSpec_unfold]
      iexact H
    iapply HΦ
    unfold fileutil.lockPost
    iexists x
    iright
    isplitr
    · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
    iexists false
    iexact HA
  subst he
  wp_auto
  wp_apply wp_Fd f fd path (DFrac.own 1) $$ Hf as Hf
  ihave Ht := lockTok_none (GF := GF) .ofd fd (openFd i (flag ||| W64 0x80000))
    (by simp [OsFd.lk, openFd])
  wp_apply syscall.FcntlFlock.wp_lock fd (W64 38) flock_ptr w (openFd i (flag ||| W64 0x80000))
    (some true) (.inr rfl) hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2 (by rw [hw.1]; rfl)
    (fun _ => hwr) (fun h => by cases h) (fun _ => rfl) $$ [Hinv flock Hfd Ht] as %e ⟨-, Hout⟩
  · iframe; isplitl []; iexact Hinv; iexact Ht
  icases fileutil.lockOut_split .ofd fd i flag e $$ Hout with (⟨%he, Hfd, Hk⟩ | ⟨%he, Hfd, Hlt⟩)
  · subst he
    have h0 : errnoErr (0 : w64) = interface.nil := by unfold errnoErr; simp
    rw [h0]
    iapply wp_fupd
    wp_auto
    ipersist «$r0»
    imodintro
    iapply HΦ
    unfold fileutil.lockPost
    iexists x
    ileft
    isplitr
    · ipureintro; rfl
    iframe HA
    iexists f, fd, i, LockKind.ofd
    iframe Hf Hoff Hfd Hk Hkind
    isplitr
    · ipureintro; exact hfi
    unfold fileutil.lockedFile
    iexact «$r0»
  · have hne : errnoErr e = interface.mkOk syscall.Errno.ty #e := by unfold errnoErr; simp only [he, ↓reduceIte]
    rw [hne]
    wp_auto
    wp_apply wp_Close f fd path _ $$ [Hinv Hf Hfd Hlt] as %cerr ⟨Hf, -⟩
    · iframe; iexact Hinv
    iapply HΦ
    unfold fileutil.lockPost
    iexists x
    iright
    isplitr
    · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
    iexists true
    iexact HA

theorem fileutil.wp_flockLockFile
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_Flock : syscall.Flock.spec (GF := GF) (hG := hG))
    (path : GoString) (flag : w64) (perm : w32) (P : IProp GF) (X : Type)
    (A : X → Bool → IProp GF) (C : X → Ino → Prop)
    (hopen : fileutil.OpenTriple P path flag perm A C)
    (hwr : decide ((flag ||| W64 0x80000).toNat % 4 ≠ O_RDONLY) = true) :
    {{ osInv (GF := GF) ∗ fileutil.lockKind (GF := GF) .flock ∗ P }}
      (App (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.flockLockFile)) (Val #path))
        (Val #flag)) (Val #perm))
    {{ (lf : Loc) (err : GoInterface), RET (PairV #lf #err); fileutil.lockPost A C path flag lf err }} := by
  wp_start as ⟨#Hinv, #Hkind, HP⟩
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
    unfold fileutil.lockPost
    iexists x
    iright
    isplitr
    · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
    iexists false
    iexact HA
  subst he
  wp_auto
  wp_apply wp_Fd f fd path (DFrac.own 1) $$ Hf as Hf
  ihave Ht := lockTok_none (GF := GF) .flock fd (openFd i (flag ||| W64 0x80000))
    (by simp [OsFd.lk, openFd])
  wp_apply wp_Flock fd (W64 2) (openFd i (flag ||| W64 0x80000)) (some true) false
    (by rfl) (fun _ => rfl) $$ [Hinv Hfd Ht] as %e Hout
  · iframe; isplitl []; iexact Hinv; iexact Ht
  icases fileutil.lockOut_split .flock fd i flag e $$ Hout with (⟨%he, Hfd, Hk⟩ | ⟨%he, Hfd, Hlt⟩)
  · subst he
    have h0 : errnoErr (0 : w64) = interface.nil := by unfold errnoErr; simp
    rw [h0]
    iapply wp_fupd
    wp_auto
    ipersist «$r0»
    imodintro
    iapply HΦ
    unfold fileutil.lockPost
    iexists x
    ileft
    isplitr
    · ipureintro; rfl
    iframe HA
    iexists f, fd, i, LockKind.flock
    iframe Hf Hoff Hfd Hk Hkind
    isplitr
    · ipureintro; exact hfi
    unfold fileutil.lockedFile
    iexact «$r0»
  · have hne : errnoErr e = interface.mkOk syscall.Errno.ty #e := by
      unfold errnoErr; simp only [he, ↓reduceIte]
    rw [hne]
    wp_auto
    wp_apply wp_Close f fd path _ $$ [Hinv Hf Hfd Hlt] as %cerr ⟨Hf, -⟩
    · iframe; iexact Hinv
    iapply HΦ
    unfold fileutil.lockPost
    iexists x
    iright
    isplitr
    · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
    iexists true
    iexact HA

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.LockFile.wp_proof
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_Flock : syscall.Flock.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.LockFile.spec (GF := GF) (hG := hG) := by
  intro path flag perm P X A C hopen hwr
  wp_start as ⟨#Hinv, #Hpkg, HP⟩
  ihave #Hdef := fileutil.pkgInit_fact $$ Hpkg
  icases Hdef with ⟨⟨%ofd, #Hlk, #HlkT⟩, -, -⟩
  wp_auto
  cases ofd
  · ihave #Hkind : fileutil.lockKind (GF := GF) .flock $$ []
    · unfold fileutil.lockKind; iexists false; iframe Hlk HlkT; ipureintro; rfl
    simp only [fileutil.lockFn, Bool.false_eq_true, ↓reduceIte]
    wp_apply fileutil.wp_flockLockFile wp_Fd wp_Close wp_Flock path flag perm P X A C hopen hwr
      $$ [HP] as %lf %err H
    · iframe; isplitl []; iexact Hinv; iexact Hkind
    iapply HΦ $$ H
  · ihave #Hkind : fileutil.lockKind (GF := GF) .ofd $$ []
    · unfold fileutil.lockKind; iexists true; iframe Hlk HlkT; ipureintro; rfl
    simp only [fileutil.lockFn, ↓reduceIte]
    wp_apply fileutil.wp_ofdLockFile wp_Fd wp_Close wp_Errorf path flag perm P X A C hopen hwr
      $$ [HP] as %lf %err H
    · iframe; isplitl []; iexact Hinv; isplitl []; iexact Hpkg; iexact Hkind
    iapply HΦ $$ H

end proof

end EtcdGrove
end Perennial
