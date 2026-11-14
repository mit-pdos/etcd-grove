/-
`os`'s directory calls in the tree's shared mode (`NsS.lean`) with the error they return made
explicit (`os.errnoPathErr err e`: a `*PathError` of the errno `e`), and their `ENOENT`-free forms
(the semantics' `ENOENT` rule, `GooseLang/Ext/Fs/Impl.lean`, 2026-11-14, pending review):
`OpenFile`/`Open` read-only of the directory `d/b` through a fraction of a claim of `d`'s directory
holding it (`wp_dirChildS`), `(*File).Readdirnames(-1)` of its fd with the same claim
(`wp_dirChildS`), and `Open` of a name holding nothing (`wp_absentErrS`). What `wal.Exist` needs to
tell a missing WAL directory from a present one (`errors.Is(err, os.ErrNotExist)`,
`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/ExistCallees.lean`). Lean-first.
-/
module

public import LinuxFs.Proof.os.NsAbsentS

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

namespace os

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `err` is a `*PathError` whose `Err` is the errno `e` (`errnoErr e`), its fields persistent: what
`os`'s models return on a failed system call (`model.pathError`, `model.wrapErrno`). -/
def errnoPathErr (err : GoInterface) (e : w64) : IProp GF :=
  iprop(∃ (pe : Loc) (op path : GoString),
    ⌜err = interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe⌝ ∗
    structFieldRef io.fs.PathError go!"Op" pe ↦□ op ∗
    structFieldRef io.fs.PathError go!"Path" pe ↦□ path ∗
    structFieldRef io.fs.PathError go!"Err" pe ↦□ errnoErr e)

instance errnoPathErr_persistent (err : GoInterface) (e : w64) :
    Persistent (errnoPathErr (GF := GF) err e) := by
  unfold errnoPathErr; infer_instance

theorem errnoPathErr_ne (err : GoInterface) (e : w64) :
    errnoPathErr (GF := GF) err e ⊢ ⌜err ≠ interface.nil⌝ := by
  unfold errnoPathErr
  iintro ⟨%pe, %op, %path, %h, -⟩
  ipureintro; subst h; intro h; cases h

end defs

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : os.Assumptions]

/-- A `*PathError` of a nonzero errno is one `fmt` formats. -/
theorem errnoPathErr_fmtErrorOk (err : GoInterface) (e : w64) (he : e ≠ 0) :
    errnoPathErr (GF := GF) err e ⊢ EtcdGrove.fmtErrorOk (GF := GF) err := by
  unfold errnoPathErr
  iintro ⟨%pe, %op, %path, %h, #Op, #Path, #Err⟩
  subst h
  iapply (pathError_fmtErrorOk pe op path (errnoErr e)) $$ Op Path Err
  iapply (errnoErr_fmtErrorOk e he)

theorem errnoPathErr_fmtErrorOkOrNil (err : GoInterface) (e : w64) (he : e ≠ 0) :
    errnoPathErr (GF := GF) err e ⊢ EtcdGrove.fmtErrorOkOrNil (GF := GF) err := by
  iintro #H
  iapply (EtcdGrove.fmtErrorOkOrNil_of _)
  iapply (errnoPathErr_fmtErrorOk err e he) $$ H

/-- `&PathError{op, path, Errno(e)}` (`model.pathError`): `errnoPathErr`. -/
theorem wp_pathError_errno (op path : GoString) (e : w64) (Φ : val → IProp GF) :
    (∀ err : GoInterface, errnoPathErr (GF := GF) err e -∗ Φ #err) ⊢
      WP (App (App (App (Val os.model.pathError) (Val #op)) (Val #path))
        (App (Val syscall.model.errno) (Val #e))) {{ Φ }} := by
  iintro HΦ
  wp_apply wp_errno
  unfold os.model.pathError
  iapply wp_fupd
  wp_auto
  iStructNamed pe
  ipersist Op
  ipersist Path
  ipersist Err
  imodintro
  iapply HΦ
  unfold errnoPathErr
  iexists pe_ptr, op, path
  isplitr
  · ipureintro; rfl
  iframe Op Path Err

/-- `f.wrapErr(op, Errno(e))` (`model.wrapErrno`): `errnoPathErr`. -/
theorem wp_wrapErrno_errno (op : GoString) (inner : Loc) (name : GoString) (e : w64)
    (Φ : val → IProp GF) :
    structFieldRef os.file go!"name" inner ↦□ name -∗
      (∀ err : GoInterface, errnoPathErr (GF := GF) err e -∗ Φ #err) -∗
      WP (App (App (App (Val os.model.wrapErrno) (Val #op)) (Val #inner)) (Val #e)) {{ Φ }} := by
  iintro #Hn HΦ
  unfold os.model.wrapErrno os.model.pathError
  rw [file_ty_eq]
  wp_auto
  iapply wp_fupd
  wp_apply wp_errno
  iStructNamed pe
  ipersist Op
  ipersist Path
  ipersist Err
  imodintro
  iapply HΦ
  unfold errnoPathErr
  iexists pe_ptr, op, name
  isplitr
  · ipureintro; rfl
  iframe Op Path Err

end wps

end os

namespace EtcdGrove

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj]

/-- `os.OpenFile(d/b, O_RDONLY, perm)` of the directory `J` that `d/b` holds (a fraction of a claim
on names of `d`'s directory containing `b`): a shared directory fd on `J`, or a `*PathError` of an
errno other than `ENOENT`. -/
theorem os.OpenFile.wp_dirChildS (d b : GoString) (perm : w32) (R : Roots) (jp J : Ino)
    (Np : NameSet) (dq dqn : DFrac) (hp : NamesH) (qc : Qp) (hb : NameOk b) (hNp : Np.Mem b)
    (hJ : hp.cur !! b = some (.dir J)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq jp ∗ osNames jp Np dqn hp ∗
        osCallPerm qc }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #(W64 0))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq jp ∗
        osNames jp Np dqn hp ∗ osCallPerm qc ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd (child d b) (DFrac.own 1) ∗
            osDirFdS fd J .idle) ∨
         (∃ e : w64, ⌜e ≠ 0 ∧ e ≠ ENOENT ∧ f = null⌝ ∗ os.errnoPathErr err e)) }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm Hp Hn HΦ
  wp_apply wp_osCallBeginS R qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [os.file_ty_eq, os.File_ty_eq]
  rw [show (W64 0 ||| W64 524288) = flRO from by decide]
  (try wp_auto)
  wp_apply wp_osOpenDirChildS R d b jp J Np dq dqn hp t s0 qc hb hNp hJ CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %fd %e %hres Hperm Hp Hn Hfd
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
    have hne : e ≠ ENOENT := by
      rcases hres with ⟨h0, -⟩ | ⟨-, h1, -⟩
      · exact absurd h0 he0
      · exact h1
    rw [decide_eq_false he0]
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      iapply IH $$ Hperm Hp Hn HΦ
    · rw [decide_eq_false he4]
      wp_auto
      wp_apply os.wp_pathError_errno as %err #Herr
      iapply HΦ
      iframe
      iright
      iexists e
      iframe Herr
      ipureintro; exact ⟨he0, hne, rfl⟩

/-- `os.Open(d/b)` of the directory `J` that `d/b` holds: `OpenFile(d/b, O_RDONLY, 0)`. -/
theorem os.Open.wp_dirChildS (d b : GoString) (R : Roots) (jp J : Ino) (Np : NameSet)
    (dq dqn : DFrac) (hp : NamesH) (qc : Qp) (hb : NameOk b) (hNp : Np.Mem b)
    (hJ : hp.cur !! b = some (.dir J)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq jp ∗ osNames jp Np dqn hp ∗
        osCallPerm qc }}
      (App (Val (@! os.Open)) (Val #(child d b)))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq jp ∗
        osNames jp Np dqn hp ∗ osCallPerm qc ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd (child d b) (DFrac.own 1) ∗
            osDirFdS fd J .idle) ∨
         (∃ e : w64, ⌜e ≠ 0 ∧ e ≠ ENOENT ∧ f = null⌝ ∗ os.errnoPathErr err e)) }} := by
  wp_start as ⟨#Hinv, #Hsi, Hp, Hn, Hperm⟩
  wp_auto
  wp_apply os.OpenFile.wp_dirChildS d b (W32 0) R jp J Np dq dqn hp qc hb hNp hJ
    $$ [Hinv Hsi Hp Hn Hperm] as %f %err Hr
  · iframe; isplitl [] <;> iassumption
  iapply HΦ
  iexact Hr

/-- `os.OpenFile(d/b, flag, perm)`, `flag` without `O_CREAT` and `O_TRUNC`, of a name holding
nothing: a `*PathError` of a nonzero errno (`OpenFile.wp_absentS` with the error made explicit). -/
theorem os.OpenFile.wp_absentErrS (d b : GoString) (flag : w64) (perm : w32) (R : Roots) (j : Ino)
    (N : NameSet) (dq dqn : DFrac) (h : NamesH) (qc : Qp)
    (hfl : OpenFlagsOk (flag ||| W64 0x80000).toNat)
    (hcr : (flag ||| W64 0x80000).toNat / O_CREAT % 2 = 0)
    (htr : (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 0) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = none) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm qc }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #flag)) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osNames j N dqn h ∗
        osCallPerm qc ∗ ∃ e : w64, ⌜e ≠ 0 ∧ f = null⌝ ∗ os.errnoPathErr err e }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  generalize hfl' : flag ||| W64 0x80000 = fl at hfl hcr htr ⊢
  imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  iloeb as IH generalizing Hperm Hp Hn HΦ
  wp_apply wp_osCallBeginS R qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [os.file_ty_eq, os.File_ty_eq, show flag ||| W64 524288 = fl from hfl']
  (try wp_auto)
  wp_apply +noauto wp_osOpenAbsentS R d b j N dq dqn h t s0 qc fl hfl hcr htr hb hN hi
    CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk
    as %e %he0 Hperm Hp Hn
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
  wp_apply os.wp_pathError_errno as %err #Herr
  iapply HΦ
  iframe
  iexists e
  iframe Herr
  ipureintro; exact ⟨he0, rfl⟩

/-- `os.Open(d/b)` of a name holding nothing: a `*PathError` of a nonzero errno. -/
theorem os.Open.wp_absentErrS (d b : GoString) (R : Roots) (j : Ino) (N : NameSet)
    (dq dqn : DFrac) (h : NamesH) (qc : Qp) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = none) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm qc }}
      (App (Val (@! os.Open)) (Val #(child d b)))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osNames j N dqn h ∗
        osCallPerm qc ∗ ∃ e : w64, ⌜e ≠ 0 ∧ f = null⌝ ∗ os.errnoPathErr err e }} := by
  wp_start as ⟨#Hinv, #Hsi, Hp, Hn, Hperm⟩
  wp_auto
  have e : W64 0 ||| W64 0x80000 = flRO := by decide
  wp_apply os.OpenFile.wp_absentErrS d b (W64 0) (W32 0) R j N dq dqn h qc
    (by rw [e]; exact flRO_ok) (by rw [e]; decide) (by rw [e]; decide) hb hN hi
    $$ [Hinv Hsi Hp Hn Hperm] as %f %err Hr
  · iframe; isplitl [] <;> iassumption
  iapply HΦ
  iexact Hr

/-- `File.Readdirnames.wp_dirS` of the fd of the directory `j` that `d/b` holds (with a fraction of a
claim on names of `d`'s directory containing `b`): an error is a `*PathError` of an errno other than
`ENOENT`. With a fraction of a claim
on names `N` of its directory: every name returned is valid; a name of `N` is returned iff it is
there, at most once; or an error. -/
theorem os.File.Readdirnames.wp_dirChildS (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac)
    (R : Roots) (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH) (n : w64) (hn : sint.Z n ≤ 0)
    (d b : GoString) (jp : Ino) (Np : NameSet) (dqp dqn : DFrac) (hp : NamesH) (hb : NameOk b)
    (hNp : Np.Mem b) (hJ : hp.cur !! b = some (.dir j)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ os.ownFile (GF := GF) f fd name dqf ∗
        osDirFdS fd j .idle ∗ osNames j N dq h ∗ osPathS R d dqp jp ∗ osNames jp Np dqn hp }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Readdirnames")) (Val #n))
    {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); os.ownFile f fd name dqf ∗
        osNames j N dq h ∗ osPathS R d dqp jp ∗ osNames jp Np dqn hp ∗
        ((∃ names : List GoString, ⌜err = interface.nil ∧ (∀ b ∈ names, NameOk b) ∧
              (∀ b, N.Mem b → ((h.cur !! b).isSome ↔ b ∈ names)) ∧
              (∀ b, N.Mem b → names.count b ≤ 1)⌝ ∗ sl ↦* names ∗
            osDirFdS fd j .done) ∨
         ((∃ e : w64, ⌜e ≠ 0 ∧ e ≠ ENOENT⌝ ∗ os.errnoPathErr err e) ∗
            ∃ r0 rs, osDirFdS fd j (.reading N r0 rs))) }} := by
  unfold os.ownFile
  wp_start as ⟨#Hinv, #Hsi, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hcl, Hpp, Hnp⟩
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
      (∀ b, N.Mem b → rs.count b ≤ 1)⌝ $$ []
  · ipureintro; subst hrs hfresh; simp
  clear hfresh hrs hsl0
  wp_auto
  iloeb as IH generalizing %fresh %rs %r0 %sl0 Hp Hosfd Hsl Hcap Hcl Hpp Hnp
  icases Hp with %Hp
  obtain ⟨hfr, hr0, hin, hcnt⟩ := Hp
  wp_apply wp_osDirReadNextChildS R fd d b jp j Np dqp dqn hp N r0 rs fresh dq h hb hNp hJ hfr hr0
    CoPset.subseteq_top CoPset.subseteq_top $$ Hinv Hsi Hosfd Hcl Hpp Hnp
    as %v Hcl Hpp Hnp ⟨%r0', %hr1, %hr2, Hv⟩
  icases Hv with (⟨%b, %hv, Hosfd⟩ | ⟨%hv, Hosfd⟩ | ⟨%e, %hv, Hosfd⟩)
  · obtain ⟨rfl, hb, hbr⟩ := hv
    wp_auto
    wp_apply wp_slice_literal (V := GoString) [b]
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl1] as %sl' ⟨Hsl, Hcap, -⟩
    iapply IH $$ %false %(b :: rs) %r0' %sl' [] [Hosfd] [Hsl] Hcap Hcl Hpp Hnp HΦ Hfd
    · ipureintro
      refine ⟨fun h => absurd h Bool.false_ne_true, fun _ => ?_, ?_, ?_⟩
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
    refine ⟨rfl, fun x hx => (hin x (List.mem_reverse.1 hx)).1, fun x hx => ?_, fun x hx => ?_⟩
    · rw [List.mem_reverse]
      exact ⟨hall x hx, fun hm => (hin x hm).2 hx⟩
    · rw [List.count_reverse]; exact hcnt x hx
  · obtain ⟨he, hne, rfl⟩ := hv
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ %false %rs %r0' %sl0 [] [Hosfd] Hsl Hcap Hcl Hpp Hnp HΦ Hfd
      · ipureintro
        refine ⟨fun h => absurd h Bool.false_ne_true, fun _ => ?_, hin, hcnt⟩
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
      · iexists e; iframe Herr; ipureintro; exact ⟨he, hne⟩
      iexists r0', rs
      iexact Hosfd

end proof

end EtcdGrove
end Perennial

end
