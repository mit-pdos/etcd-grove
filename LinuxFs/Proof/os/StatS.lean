/-
`os.Stat` (the draft model `TrustedCode/os.lean`'s `model.stat`: an `open(O_RDONLY)`, `FdKind`, an
`fstat` of a file, the fd closed) in the tree's shared mode (`GooseLang/Ext/Fs/TreeShared.lean`), for
the WAL's uses (`fileutil.Exist`, `CheckDirPermission`, `TouchDirAll`): of a directory (a spine to
it), and of a name holding nothing (a fraction of a claim on it). Plain triples (no claim changes);
each attempt a `CallBegin` with a fraction `qc` of the call permission, which comes back. The
directory's `fileStat` is only `ownFileStat` (some size and mode: the mode's directory bit is not
yet stated). A regular file's `Stat` (which needs its `OsMeta` for the `fstat`) is not stated.
Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.OpenFile
public import LinuxFs.Proof.os.SharedExt

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
variable [os.Assumptions] [os.fileStat.FieldAssumptions] [go.BasicIntoValInj]

/-- `os.Stat(p)` of the directory `J` (a spine to it): a `fileStat`, or an error. -/
theorem os.Stat.wp_dirS (p : GoString) (R : Roots) (J : Ino) (dq : DFrac) (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗ osCallPerm qc }}
      (App (Val (@! os.Stat)) (Val #p))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R p dq J ∗
        osCallPerm qc ∗
        ((∃ (fs : Loc) (sz : w64), ⌜err = interface.nil ∧
            fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
            os.ownFileStat fs sz) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm⟩
  imod osLogLb_0 with #Hlb
  unfold os.model.stat os.model.arbitraryMode
  rw [os.fileStat_ty_eq]
  wp_auto
  iloeb as IH generalizing Hperm Hp HΦ
  wp_apply wp_osCallBeginS R qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [show W64 0x80000 = flRO from rfl]
  wp_apply wp_osOpenDirS R p J dq t s0 qc CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hp Hk as %fd %e %hres Hperm Hp Hfd
  by_cases he4 : e = W64 4
  · iclear Hfd
    rw [decide_eq_true he4]
    wp_auto
    try rw [os.fileStat_ty_eq]
    iapply IH $$ Hperm Hp HΦ
  rw [decide_eq_false he4]
  wp_auto
  by_cases he0 : e = W64 0
  · subst he0
    ihave Hfd := Hfd $$ %rfl
    rw [decide_eq_true rfl]
    wp_auto
    wp_apply wp_osFdKindDirS fd J .idle CoPset.subseteq_top $$ Hos Hfd as Hfd
    wp_apply wp_ArbitraryInt as %sz _
    iapply wp_fupd
    wp_apply wp_osDirCloseS fd J .idle CoPset.subseteq_top $$ Hos Hfd as %e2
    iStructNamed fs
    wp_auto
    wp_apply wp_ArbitraryInt as %x _
    ipersist size
    ipersist mode
    imodintro
    iapply HΦ
    iframe
    ileft
    iexists fs_ptr, _
    unfold os.ownFileStat
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl []
    · iassumption
    iexists _
    iassumption
  · iclear Hfd
    rw [decide_eq_false he0]
    wp_auto
    unfold os.model.pathError
    wp_apply wp_errno
    iapply HΦ
    iframe
    iright
    ipureintro; intro hc; cases hc

/-- `os.Stat(d/b)` of a name holding nothing (a fraction of a claim on names containing `b`): an
error, no effect. -/
theorem os.Stat.wp_absentS (d b : GoString) (R : Roots) (j : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (qc : Qp) (hb : NameOk b) (hN : N.Mem b) (hi : h.cur !! b = none) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm qc }}
      (App (Val (@! os.Stat)) (Val #(child d b)))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R d dq j ∗
        osNames j N dqn h ∗ osCallPerm qc ∗ ⌜err ≠ interface.nil⌝ }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  imod osLogLb_0 with #Hlb
  unfold os.model.stat
  wp_auto
  iloeb as IH generalizing Hperm Hp Hn HΦ
  wp_apply wp_osCallBeginS R qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  wp_apply wp_osOpenAbsentS R d b j N dq dqn h t s0 qc (W64 0x80000)
    (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) (by decide) hb hN hi CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk
    as %e %he Hperm Hp Hn
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    iapply IH $$ Hperm Hp Hn HΦ
  rw [decide_eq_false he4]
  wp_auto
  rw [decide_eq_false (show e ≠ W64 0 from he)]
  wp_auto
  unfold os.model.pathError
  wp_apply wp_errno
  iapply HΦ
  iframe
  ipureintro; intro hc; cases hc

end proof

end EtcdGrove
end Perennial
