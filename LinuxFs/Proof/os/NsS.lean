/-
Specs of `os`'s trusted models (`TrustedCode/os.lean`) on the directory tree in its shared mode
(`GooseLang/Ext/Fs/TreeShared.lean`; `notes/wal-fsext-i2-design.md`), for the calls that change no
claim (plain triples, no atomic update): `OpenFile` of an existing file without `O_TRUNC` (any
access mode: the WAL's `LockFile(O_WRONLY)`, `openWALFiles`' `O_RDWR`/`O_RDONLY`), `OpenFile`/`Open`
read-only of a directory (a shared directory fd, holding nothing), `(*File).Readdirnames(-1)` of
such an fd (exact on the names of a claim the caller shows, a fraction of it; any valid name
elsewhere), and its `Close`. Each attempt is a `CallBegin` with a fraction `qc` of the call
permission, which comes back. Lean-first (no Rocq counterpart); the legacy counterparts are
`Proof/os/Ns.lean`'s.
-/
module

public import LinuxFs.Proof.os.OpenFile
public import LinuxFs.Proof.os.File__Close
public import LinuxFs.Proof.os.SharedExt
public import LinuxFs.Proof.os.ErrorOk
public import LinuxFs.Proof.os.Off
public import LinuxFs.Proof.os.ErrnoPathErr

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
variable [os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj]

/-- `os.OpenFile(d/b, flag, perm)` of a name holding the file `i`, `flag` without `O_TRUNC`, with
a fraction of a claim on names containing `b`: a fresh fd on `i` with `flag`'s access mode, or an
error. Nothing is logged (an `O_CREAT` of an existing file creates nothing). -/
theorem os.OpenFile.wp_fileS (d b : GoString) (flag : w64) (perm : w32) (R : Roots) (j i : Ino)
    (N : NameSet) (dq dqn : DFrac) (h : NamesH) (qc : Qp)
    (hfl : OpenFlagsOk (flag ||| W64 0x80000).toNat)
    (htr : (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 0) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm qc }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #flag)) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osNames j N dqn h ∗
        osCallPerm qc ∗
        ((∃ fd : w64, ⌜err = interface.nil ∧ 0 ≤ fd.toInt⌝ ∗ os.ownFile f fd (child d b) (DFrac.own 1) ∗
            os.ownOff f (W64 0) ∗
            osFd fd (DFrac.own 1) (openFd i (flag ||| W64 0x80000))) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝ ∗ fmtErrorOkOrNil err) }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  generalize hfl' : flag ||| W64 0x80000 = fl at hfl htr ⊢
  imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  iloeb as IH generalizing Hperm Hp Hn HΦ
  wp_apply wp_osCallBeginS R qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [os.file_ty_eq, os.File_ty_eq, show flag ||| W64 524288 = fl from hfl']
  (try wp_auto)
  wp_apply +noauto wp_osOpenFileS R d b j i N dq dqn h t s0 qc fl hfl htr hb hN hi
    CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk
    as %fd %e %hres Hperm Hp Hn Hfd
  by_cases he0 : e = W64 0
  · subst he0
    have hfd0 : 0 ≤ fd.toInt := by rcases hres with ⟨-, h⟩ | ⟨h, -⟩; exact h; exact absurd rfl h
    ihave Hfd := (show (if W64 0 = (0 : w64) then osFd (GF := GF) fd (DFrac.own 1)
        (openFd i fl) else emp) ⊢ osFd fd (DFrac.own 1) (openFd i fl)
      by split
         · iintro H; iexact H
         · exact absurd rfl ‹_›) $$ Hfd
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    iapply HΦ
    iframe
    ileft
    iexists fd
    iframe
    isplitr
    · ipureintro; exact ⟨rfl, hfd0⟩
    unfold os.ownFile os.ownOff
    isplitr [off]
    · iexists inner_ptr
      iframe
      isplitl [] <;> iassumption
    · iexists inner_ptr
      iframe
      iassumption
  · iclear Hfd
    have hfd : fd = -1 := by rcases hres with ⟨h, -⟩ | ⟨-, h⟩; exact absurd h he0; exact h
    subst hfd
    wp_auto
    rw [decide_eq_false (show e ≠ W64 0 from he0)]
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      iapply IH $$ Hperm Hp Hn HΦ
    rw [decide_eq_false (show e ≠ W64 4 from he4)]
    wp_auto
    wp_apply os.wp_pathError_ok _ _ e he0 as %pe #Hok
    iapply HΦ
    iframe
    iright
    isplitr
    · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
    iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok

/-- `os.OpenFile(p, O_RDONLY, perm)` of the directory `j` (a spine to it): a shared directory fd,
not read, holding nothing; or a `*PathError` of a nonzero errno. -/
theorem os.OpenFile.wp_dirErrS (p : GoString) (perm : w32) (R : Roots) (j : Ino) (dq : DFrac)
    (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq j ∗ osCallPerm qc }}
      (App (App (App (Val (@! os.OpenFile)) (Val #p)) (Val #(W64 0))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R p dq j ∗ osCallPerm qc ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗
            osDirFdS fd j .idle) ∨
         (∃ e : w64, ⌜e ≠ 0 ∧ f = null⌝ ∗ os.errnoPathErr err e)) }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm⟩
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm Hp HΦ
  wp_apply wp_osCallBeginS R qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [os.file_ty_eq, os.File_ty_eq]
  rw [show (W64 0 ||| W64 524288) = flRO from by decide]
  (try wp_auto)
  wp_apply wp_osOpenDirS R p j dq t s0 qc CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hp Hk as %fd %e %hres Hperm Hp Hfd
  by_cases he0 : e = W64 0
  · subst he0
    ihave Hfd := Hfd $$ %rfl
    rw [decide_eq_true rfl]
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    iapply HΦ
    iframe
    ileft
    iexists fd
    iframe
    isplitr
    · ipureintro; rfl
    unfold os.ownFile
    iexists inner_ptr
    iframe
    isplitl [] <;> iassumption
  · iclear Hfd
    rw [decide_eq_false he0]
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      iapply IH $$ Hperm Hp HΦ
    · rw [decide_eq_false he4]
      wp_auto
      wp_apply os.wp_pathError_errno as %err #Herr
      iapply HΦ
      iframe
      iright
      iexists e
      iframe Herr
      ipureintro; exact ⟨he0, rfl⟩

/-- `os.OpenFile(p, O_RDONLY, perm)` of the directory `j` (a spine to it): a shared directory fd,
not read, holding nothing; or an error. -/
theorem os.OpenFile.wp_dirS (p : GoString) (perm : w32) (R : Roots) (j : Ino) (dq : DFrac)
    (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq j ∗ osCallPerm qc }}
      (App (App (App (Val (@! os.OpenFile)) (Val #p)) (Val #(W64 0))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R p dq j ∗ osCallPerm qc ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗
            osDirFdS fd j .idle) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝) }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm⟩
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm Hp HΦ
  wp_apply wp_osCallBeginS R qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [os.file_ty_eq, os.File_ty_eq]
  rw [show (W64 0 ||| W64 524288) = flRO from by decide]
  (try wp_auto)
  wp_apply wp_osOpenDirS R p j dq t s0 qc CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hp Hk as %fd %e %hres Hperm Hp Hfd
  by_cases he0 : e = W64 0
  · subst he0
    ihave Hfd := Hfd $$ %rfl
    rw [decide_eq_true rfl]
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    iapply HΦ
    iframe
    ileft
    iexists fd
    iframe
    isplitr
    · ipureintro; rfl
    unfold os.ownFile
    iexists inner_ptr
    iframe
    isplitl [] <;> iassumption
  · iclear Hfd
    rw [decide_eq_false he0]
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      iapply IH $$ Hperm Hp HΦ
    · rw [decide_eq_false he4]
      wp_auto
      unfold os.model.pathError
      wp_apply wp_errno
      iapply HΦ
      iframe
      iright
      ipureintro; exact ⟨(fun h => by cases h), rfl⟩

/-- `os.Open(p)` of the directory `j`, the error explicit: `OpenFile(p, O_RDONLY, 0)`. -/
theorem os.Open.wp_dirErrS (p : GoString) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq j ∗ osCallPerm qc }}
      (App (Val (@! os.Open)) (Val #p))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R p dq j ∗ osCallPerm qc ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗
            osDirFdS fd j .idle) ∨
         (∃ e : w64, ⌜e ≠ 0 ∧ f = null⌝ ∗ os.errnoPathErr err e)) }} := by
  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm⟩
  wp_auto
  wp_apply os.OpenFile.wp_dirErrS p (W32 0) R j dq qc $$ [Hinv Hsi Hp Hperm] as %f %err Hr
  · iframe; isplitl [] <;> iassumption
  iapply HΦ
  iexact Hr

/-- `os.Open(p)` of the directory `j`: `OpenFile(p, O_RDONLY, 0)`. -/
theorem os.Open.wp_dirS (p : GoString) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq j ∗ osCallPerm qc }}
      (App (Val (@! os.Open)) (Val #p))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R p dq j ∗ osCallPerm qc ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗
            osDirFdS fd j .idle) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝) }} := by
  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm⟩
  wp_auto
  wp_apply os.OpenFile.wp_dirS p (W32 0) R j dq qc $$ [Hinv Hsi Hp Hperm] as %f %err Hr
  · iframe; isplitl [] <;> iassumption
  iapply HΦ
  iexact Hr

/-- `f.Close()` of a shared directory fd: any error; the fd gone. -/
theorem os.File.Close.wp_dirS (f : Loc) (fd : w64) (name : GoString) (j : Ino) (ph : DirPhS) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name (DFrac.own 1) ∗ osDirFdS fd j ph }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #()))
    {{ (err : GoInterface), RET #err; emp }} := by
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  ihave %hnn := typedPointsto_not_null _ _ _ $$ Hf
  rw [decide_eq_false hnn]
  wp_auto
  wp_apply wp_osFdKindDirS fd j ph CoPset.subseteq_top $$ Hinv Hosfd as Hosfd
  wp_apply wp_osDirCloseS fd j ph CoPset.subseteq_top $$ Hinv Hosfd as %e
  by_cases he : e = W64 0
  · rw [decide_eq_true he]
    wp_auto
    iapply HΦ
    iempintro
  · rw [decide_eq_false he]
    wp_auto
    wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
    iapply HΦ
    iempintro

/-- `f.Readdirnames(n)`, `n ≤ 0`, of a shared directory fd not yet read, with a fraction of a claim
on names `N` of its directory: every name returned is valid; a name of `N` is returned iff it is
there, at most once; or an error. -/
theorem os.File.Readdirnames.wp_dirS (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac)
    (R : Roots) (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH) (n : w64) (hn : sint.Z n ≤ 0) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ os.ownFile (GF := GF) f fd name dqf ∗
        osDirFdS fd j .idle ∗ osNames j N dq h }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Readdirnames")) (Val #n))
    {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); os.ownFile f fd name dqf ∗
        osNames j N dq h ∗
        ((∃ names : List GoString, ⌜err = interface.nil ∧ (∀ b ∈ names, NameOk b) ∧
              (∀ b, N.Mem b → ((h.cur !! b).isSome ↔ b ∈ names)) ∧
              (∀ b, N.Mem b → names.count b ≤ 1) ∧ names.length ≤ 2 ^ 44⌝ ∗ sl ↦* names ∗
            osDirFdS fd j .done) ∨
         ((∃ e : w64, ⌜e ≠ 0⌝ ∗ os.errnoPathErr err e) ∗
            ∃ r0 rs, osDirFdS fd j (.reading N r0 rs))) }} := by
  unfold os.ownFile
  wp_start as ⟨#Hinv, #Hsi, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hcl⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z (W64 0) < sint.Z n by
    rw [show sint.Z (W64 0) = 0 from rfl]; omega)]
  wp_auto
  wp_apply wp_slice_literal (V := GoString) []
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hcap⟩
  simp only [go.arrayLiteralSize, List.foldl]
  obtain ⟨fresh, hfresh⟩ : ∃ b : Bool, b = true := ⟨_, rfl⟩
  obtain ⟨rs, hrs⟩ : ∃ rs : List GoString, rs = [] := ⟨_, rfl⟩
  obtain ⟨r0, -⟩ : ∃ r0 : Nat, r0 = 0 := ⟨_, rfl⟩
  ihave Hosfd : osDirFdS fd j (if fresh then .idle else .reading N r0 rs) $$ [Hosfd]
  · subst hfresh; simp only [↓reduceIte]; iexact Hosfd
  generalize hsl0 : slice.mk _ _ _ = sl0
  ihave Hsl : sl0 ↦* rs.reverse $$ [Hsl]
  · subst hrs; rw [List.reverse_nil]; iexact Hsl
  ihave Hp : ⌜(fresh = true → rs = []) ∧ (fresh = false → h.next ≤ r0) ∧
      (∀ b ∈ rs, NameOk b ∧ (N.Mem b → (h.cur !! b).isSome)) ∧
      (∀ b, N.Mem b → rs.count b ≤ 1) ∧ rs.length ≤ 2 ^ 44⌝ $$ []
  · ipureintro; subst hrs hfresh; simp
  clear hfresh hrs hsl0
  wp_auto
  iloeb as IH generalizing %fresh %rs %r0 %sl0 Hp Hosfd Hsl Hcap Hcl
  icases Hp with %Hp
  obtain ⟨hfr, hr0, hin, hcnt, hlen⟩ := Hp
  wp_apply wp_osDirReadNextS R fd j N r0 rs fresh dq h hfr hr0 CoPset.subseteq_top
    CoPset.subseteq_top $$ Hinv Hsi Hosfd Hcl as %v Hcl ⟨%r0', %hr1, %hr2, Hv⟩
  icases Hv with (⟨%b, %hv, Hosfd⟩ | ⟨%hv, Hosfd⟩ | ⟨%e, %hv, Hosfd⟩)
  · obtain ⟨rfl, hb, hbr⟩ := hv
    wp_auto
    ihave %hsl := ownSlice_len _ _ _ $$ Hsl
    wp_apply_core wp_assume
    iintro %hlt
    have hlt' : rs.length < 2 ^ 44 := by
      rw [List.length_reverse] at hsl
      have := of_decide_eq_true hlt
      word
    wp_auto
    wp_apply wp_slice_literal (V := GoString) [b]
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl1] as %sl' ⟨Hsl, Hcap, -⟩
    iapply IH $$ %false %(b :: rs) %r0' %sl' [] [Hosfd] [Hsl] Hcap Hcl HΦ Hfd
    · ipureintro
      refine ⟨fun h => absurd h Bool.false_ne_true, fun _ => ?_, ?_, ?_, ?_⟩
      · cases fresh
        · rw [hr1 rfl]; exact hr0 rfl
        · exact hr2 rfl
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨hb, fun hm => (hbr hm).1⟩
        · exact hin x hx
      · intro x hx
        rw [List.count_cons]
        by_cases hxb : x = b
        · subst hxb
          have := (hbr hx).2
          rw [List.count_eq_zero_of_not_mem this]; simp
        · simp only [beq_iff_eq, Ne.symm hxb, ↓reduceIte, Nat.add_zero]; exact hcnt x hx
      · rw [List.length_cons]; omega
    · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hosfd
    · rw [List.reverse_cons]; iexact Hsl
  · obtain ⟨rfl, hall⟩ := hv
    wp_auto
    iapply HΦ
    iframe
    isplitl []
    · isplitl [] <;> iassumption
    ileft
    iexists rs.reverse
    iframe
    ipureintro
    refine ⟨rfl, fun x hx => (hin x (List.mem_reverse.1 hx)).1, fun x hx => ?_, fun x hx => ?_,
      by rw [List.length_reverse]; exact hlen⟩
    · rw [List.mem_reverse]
      exact ⟨hall x hx, fun hm => (hin x hm).2 hx⟩
    · rw [List.count_reverse]; exact hcnt x hx
  · obtain ⟨he, rfl⟩ := hv
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ %false %rs %r0' %sl0 [] [Hosfd] Hsl Hcap Hcl HΦ Hfd
      · ipureintro
        refine ⟨fun h => absurd h Bool.false_ne_true, fun _ => ?_, hin, hcnt, hlen⟩
        cases fresh
        · rw [hr1 rfl]; exact hr0 rfl
        · exact hr2 rfl
      · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hosfd
    · rw [decide_eq_false he4]
      wp_auto
      rw [decide_eq_false (show ¬ e = W64 0 from he)]
      wp_auto
      wp_apply os.wp_wrapErrno_errno _ inner name e $$ Hn as %err #Herr
      iapply HΦ
      iframe
      isplitl []
      · isplitl [] <;> iassumption
      iright
      isplitr
      · iexists e; iframe Herr; ipureintro; exact he
      iexists r0', rs
      iexact Hosfd

end proof

end EtcdGrove
end Perennial
