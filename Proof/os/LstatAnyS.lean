/-
`os.Lstat(d/b)` of a name of a directory whose claim the caller holds, whatever the name holds (P3 of
the pure-premise plan, 2026-11-24: the mvcc testers' `absent`, `Lstat` then `errors.Is(err,
os.ErrNotExist)`): of a name holding nothing, a `*PathError` of a nonzero errno (`wp_absentErrS`, so
that `errors.Is` can be asked of it); of a regular file (no `OsMeta`) and of a directory (the whole
claim on the name), no error where the file system does not fail (`FsNoErrAt`): `wp_fileAnySW`,
`wp_childDirSW`. The first is `model.wp_stat_absentS` with the error made explicit, the others
`StatNE.lean`'s `model.stat` specs at `Lstat` (and, for a directory, the spine of `MkdirAllDir.lean`'s `Lstat.wp_childDirS` through
the claim). Lean-first.
-/
module

public import Proof.os.StatNE
public import Proof.os.ErrnoPathErr
public import Proof.os.MkdirAllParts

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

/-- `model.stat(op, d/b)` of a name holding nothing: a `*PathError` of a nonzero errno
(`wp_stat_absentS` with the error made explicit). -/
theorem os.model.wp_stat_absentErrS (op d b : GoString) (R : Roots) (j : Ino) (N : NameSet)
    (dq dqn : DFrac) (h : NamesH) (qc : Qp) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = none) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc }}
      (App (App (Val os.model.stat) (Val #op)) (Val #(child d b)))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R d dq j ∗
        osNames j N dqn h ∗ osCallPerm (callKey R d) qc ∗
        ∃ e : w64, ⌜e ≠ 0⌝ ∗ os.errnoPathErr err e }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  imod osLogLb_0 with #Hlb
  try unfold os.model.stat
  icases osPathS_pathIn_keep R d dq j $$ Hp with ⟨%hpin, Hp⟩
  wp_apply wp_osPathKindS R (child d b) (pathIn_child hpin.2 hb) CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi as %k %hk
  have hk2 : k ≠ W64 2 := by rcases hk with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  try wp_auto
  try rw [decide_eq_false hk2]
  try wp_auto
  iloeb as IH generalizing Hperm Hp Hn HΦ
  icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  wp_apply wp_osCallBeginS R _ qc 0 CoPset.subseteq_top CoPset.subseteq_top
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
  wp_apply os.wp_pathError_errno as %err #Herr
  iapply HΦ
  iframe
  iexists e
  iframe Herr
  ipureintro; exact he

/-- `os.Lstat(d/b)` of a name holding nothing: a `*PathError` of a nonzero errno. -/
theorem os.Lstat.wp_absentErrS (d b : GoString) (R : Roots) (j : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (qc : Qp) (hb : NameOk b) (hN : N.Mem b) (hi : h.cur !! b = none) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc }}
      (App (Val (@! os.Lstat)) (Val #(child d b)))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R d dq j ∗
        osNames j N dqn h ∗ osCallPerm (callKey R d) qc ∗
        ∃ e : w64, ⌜e ≠ 0⌝ ∗ os.errnoPathErr err e }} := by
  wp_start as Hpre
  wp_apply os.model.wp_stat_absentErrS _ d b R j N dq dqn h qc hb hN hi $$ Hpre
  iexact HΦ

/-- `os.Lstat(d/b)` of the regular file `i` (no `OsMeta`), an error only when the file system can
fail on `d/b`. -/
theorem os.Lstat.wp_fileAnySW (d b : GoString) (R : Roots) (j i : Ino) (N : NameSet)
    (dq dqn : DFrac) (h : NamesH) (qc : Qp) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc }}
      (App (Val (@! os.Lstat)) (Val #(child d b)))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R d dq j ∗
        osNames j N dqn h ∗ osCallPerm (callKey R d) qc ∗
        ((∃ (fs : Loc) (sz : w64), ⌜err = interface.nil ∧
            fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
            os.ownFileStat fs sz) ∨
         ⌜err ≠ interface.nil ∧ ¬ FsNoErrAt (child d b)⌝) }} := by
  wp_start as Hpre
  wp_apply os.model.wp_stat_fileAnySW _ d b R j i N dq dqn h qc hb hN hi $$ Hpre
  iexact HΦ

/-- `os.Lstat(p)` of the directory `J` (a spine to it), an error only when the file system can fail
on `p`. -/
theorem os.Lstat.wp_dirSW (p : GoString) (R : Roots) (J : Ino) (dq : DFrac) (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗ osCallPerm (callKey R p) qc }}
      (App (Val (@! os.Lstat)) (Val #p))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R p dq J ∗
        osCallPerm (callKey R p) qc ∗
        ((∃ (fs : Loc) (sz : w64), ⌜err = interface.nil ∧
            fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
            os.ownFileStat fs sz) ∨
         ⌜err ≠ interface.nil ∧ ¬ FsNoErrAt p⌝) }} := by
  wp_start as Hpre
  wp_apply os.model.wp_stat_dirSW $$ Hpre
  iexact HΦ

/-- `os.Lstat(d/b)` of the directory `J` at `b` (the whole claim on `b`, owned fractions), an error
only when the file system can fail on `d/b` (`os.Lstat.wp_childDirS`'s spine, at `wp_dirSW`). -/
theorem os.Lstat.wp_childDirSW (d b : GoString) (R : Roots) (j J : Ino) (qd qn : Qp) (h : NamesH)
    (qc : Qp) (hb : NameOk b) (hJ : h.cur !! b = some (.dir J)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗
        osNames j (.only [b]) (DFrac.own qn) h ∗ osCallPerm (callKey R d) qc }}
      (App (Val (@! os.Lstat)) (Val #(child d b)))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R d (DFrac.own qd) j ∗
        osNames j (.only [b]) (DFrac.own qn) h ∗ osCallPerm (callKey R d) qc ∗
        ((∃ (fs : Loc) (sz : w64), ⌜err = interface.nil ∧
            fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
            os.ownFileStat fs sz) ∨
         ⌜err ≠ interface.nil ∧ ¬ FsNoErrAt (child d b)⌝) }} := by
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩ HΦ
  obtain ⟨ε, a', b', hqd, hqq⟩ := os.qp_common qd qn
  subst hqd hqq
  icases (osPathS_frac R d ε a' j).1 $$ Hp with ⟨Hpe, Hpa⟩
  icases (osNames_frac j (.only [b]) ε b' h).1 $$ Hn with ⟨Hne, Hnb⟩
  ihave Hpc := osPathS_child R d b (DFrac.own ε) j J h hb hJ $$ Hpe Hne
  icases osCallPerm_child R d b _ j qc $$ Hpa Hperm with ⟨Hpa, Hperm⟩
  wp_apply os.Lstat.wp_dirSW (child d b) R J (DFrac.own ε) qc $$ [Hpc Hperm]
    as %fi %err ⟨Hpc, Hperm, Hres⟩
  · iframe; iframe #
  icases os.osPathS_unchild R d b j J ε a' hb $$ [Hpc Hpa] with ⟨%h'', Hp, Hne, %-⟩
  · iframe
  icases osCallPerm_unchild R d b _ j qc $$ Hp Hperm with ⟨Hp, Hperm⟩
  icases osNames_agree j (.only [b]) _ _ h'' h $$ Hne Hnb with %he
  subst he
  ihave Hn := (osNames_frac j (.only [b]) ε b' h'').2 $$ [Hne Hnb]
  · iframe
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial

end
