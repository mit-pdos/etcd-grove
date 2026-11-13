/-
`os.OpenFile`/`os.Open` without `O_CREAT` of a name holding nothing, in the tree's shared mode
(`GooseLang/Ext/Fs/TreeShared.lean`), with a fraction of a claim on names containing it: an error,
no effect (`wp_osOpenAbsentS`, retried on `EINTR`). The WAL's `openAtIndex` of a missing WAL
directory reaches it through `fileutil.ReadDir` (`os.Open(dir)`; W3/W5's gap 2,
`notes/wal-fsext-plan.md`). Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.NsS

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

/-- `os.OpenFile(d/b, flag, perm)`, `flag` without `O_CREAT` and `O_TRUNC`, of a name holding
nothing, with a fraction of a claim on names containing `b`: an error. -/
theorem os.OpenFile.wp_absentS (d b : GoString) (flag : w64) (perm : w32) (R : Roots) (j : Ino)
    (N : NameSet) (dq dqn : DFrac) (h : NamesH) (qc : Qp)
    (hfl : OpenFlagsOk (flag ||| W64 0x80000).toNat)
    (hcr : (flag ||| W64 0x80000).toNat / O_CREAT % 2 = 0)
    (htr : (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 0) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = none) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm qc }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #flag)) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osNames j N dqn h ∗
        osCallPerm qc ∗ ⌜err ≠ interface.nil ∧ f = null⌝ ∗ fmtErrorOkOrNil err }} := by
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
  wp_apply os.wp_pathError_ok _ _ e he0 as %pe #Hok
  iapply HΦ
  iframe
  isplitr
  · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
  iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok

/-- `os.Open(d/b)` of a name holding nothing: `OpenFile(d/b, O_RDONLY, 0)`, an error. -/
theorem os.Open.wp_absentS (d b : GoString) (R : Roots) (j : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (qc : Qp) (hb : NameOk b) (hN : N.Mem b) (hi : h.cur !! b = none) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm qc }}
      (App (Val (@! os.Open)) (Val #(child d b)))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osNames j N dqn h ∗
        osCallPerm qc ∗ ⌜err ≠ interface.nil ∧ f = null⌝ ∗ fmtErrorOkOrNil err }} := by
  wp_start as ⟨#Hinv, #Hsi, Hp, Hn, Hperm⟩
  wp_auto
  have e : W64 0 ||| W64 0x80000 = flRO := by decide
  wp_apply os.OpenFile.wp_absentS d b (W64 0) (W32 0) R j N dq dqn h qc (by rw [e]; exact flRO_ok)
    (by rw [e]; decide) (by rw [e]; decide) hb hN hi $$ [Hinv Hsi Hp Hn Hperm] as %f %err Hr
  · iframe; isplitl [] <;> iassumption
  iapply HΦ
  iexact Hr

end proof

end EtcdGrove
end Perennial

end
