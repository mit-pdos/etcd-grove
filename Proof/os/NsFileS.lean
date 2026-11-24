/-
`os.OpenFile`/`os.Open` without `O_TRUNC` of a name holding a file, in the tree's shared mode, through
a fraction of a claim on names containing it (`wp_fileSN`): a fresh `*os.File` at offset 0 on the file,
or a `*PathError` of an errno other than `ENOENT` (the semantics' `ENOENT` rule,
`GooseLang/Ext/Fs/Impl.lean`, 2026-11-14, pending review; the extension's `wp_osOpenFileSN'`). What
`durable`'s `tryRead` needs to tell a present file from a missing one (`errors.Is(err,
os.ErrNotExist)`). Lean-first.
-/
module

public import Proof.os.NsChildS
public import GooseLang.Ext.Fs.TreeSharedOpenFileN

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

namespace EtcdGrove

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj]

/-- `os.OpenFile(d/b, flag, perm)`, `flag` without `O_TRUNC`, of the file `i` that `d/b` holds (a
fraction of a claim on names of `d`'s directory containing `b`): a fresh `*os.File` on a fresh fd of
`i`, at offset 0, or a `*PathError` of an errno other than `ENOENT`. -/
theorem os.OpenFile.wp_fileSN (d b : GoString) (flag : w64) (perm : w32) (R : Roots) (j i : Ino)
    (N : NameSet) (dq dqn : DFrac) (h : NamesH) (qc : Qp)
    (hfl : OpenFlagsOk (flag ||| W64 0x80000).toNat)
    (htr : (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 0) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #flag)) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osNames j N dqn h ∗
        osCallPerm (callKey R d) qc ∗
        ((∃ fd : w64, ⌜err = interface.nil ∧ 0 ≤ fd.toInt⌝ ∗
            os.ownFile f fd (child d b) (DFrac.own 1) ∗ os.ownOff f (W64 0) ∗
            osFd fd (DFrac.own 1) (openFd i (flag ||| W64 0x80000))) ∨
         (∃ e : w64, ⌜e ≠ 0 ∧ e ≠ ENOENT ∧ f = null⌝ ∗ os.errnoPathErr err e)) }} := by

  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  generalize hfl' : flag ||| W64 0x80000 = fl at hfl htr ⊢
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm Hp Hn HΦ
  icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  wp_apply wp_osCallBeginS R _ qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [os.file_ty_eq, os.File_ty_eq, show flag ||| W64 524288 = fl from hfl']
  (try wp_auto)
  wp_apply wp_osOpenFileSN' R d b j i N dq dqn h t s0 qc fl hfl htr hb hN hi CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %fd %e %hres Hperm Hp Hn Hfd
  by_cases he0 : e = W64 0
  · subst he0
    have hfd0 : 0 ≤ fd.toInt := by
      rcases hres with ⟨-, h1⟩ | ⟨h0, -⟩
      · exact h1
      · exact absurd rfl h0
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
      (repeat' isplitl []) <;> iassumption
    · iexists inner_ptr
      iframe
      iassumption
  · iclear Hfd
    have hne : e ≠ ENOENT := by
      rcases hres with ⟨h0, -⟩ | ⟨-, h1, -⟩
      · exact absurd h0 he0
      · exact h1
    have hfd : fd = -1 := by rcases hres with ⟨h, -⟩ | ⟨-, -, h⟩; exact absurd h he0; exact h
    subst hfd
    rw [decide_eq_false (show e ≠ W64 0 from he0)]
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

/-- `os.Open(d/b)` of the file `i` that `d/b` holds: `OpenFile(d/b, O_RDONLY, 0)`. -/
theorem os.Open.wp_fileSN (d b : GoString) (R : Roots) (j i : Ino) (N : NameSet)
    (dq dqn : DFrac) (h : NamesH) (qc : Qp) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc }}
      (App (Val (@! os.Open)) (Val #(child d b)))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osNames j N dqn h ∗
        osCallPerm (callKey R d) qc ∗
        ((∃ fd : w64, ⌜err = interface.nil ∧ 0 ≤ fd.toInt⌝ ∗
            os.ownFile f fd (child d b) (DFrac.own 1) ∗ os.ownOff f (W64 0) ∗
            osFd fd (DFrac.own 1) (openFd i flRO)) ∨
         (∃ e : w64, ⌜e ≠ 0 ∧ e ≠ ENOENT ∧ f = null⌝ ∗ os.errnoPathErr err e)) }} := by
  have e : W64 0 ||| W64 0x80000 = flRO := by decide
  rw [← e]

  wp_start as ⟨#Hinv, #Hsi, Hp, Hn, Hperm⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  wp_auto
  wp_apply os.OpenFile.wp_fileSN d b (W64 0) (W32 0) R j i N dq dqn h qc
    (by rw [e]; exact flRO_ok) (by rw [e]; decide) hb hN hi
    $$ [Hinv Hsi Hp Hn Hperm] as %f %err Hr
  · iframe; (repeat' isplitl []) <;> iassumption
  iapply HΦ
  iexact Hr

end proof

end EtcdGrove
end Perennial
