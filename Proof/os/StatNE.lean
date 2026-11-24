/-
`os.Stat` with its error witnessed (wal-safe, 2026-11-22, step 2 (D), design (FNE) of
`notes/wal-units/tester.md`): of a directory (a spine to it) and of a regular file (a fraction of a
claim on its name; no `OsMeta`, its `fstat` by `wp_osFstatAnyW`), an error only when the file system
can fail on the path (`FsNoErrAt`): so `fileutil.Exist` of a covered path holding something answers
`true`. Lean-first.
-/
module

public import Proof.os.IgnoringEINTR
public import Perennial.Proof.internal.gomodel.Link
public import Proof.os.StatS
public import Proof.os.RemoveAllNE
public import GooseLang.Ext.Fs.FstatAny

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
variable [os.Assumptions] [go.BasicIntoValInj]

/-- `wp_stat_dirS`, an error only when the file system can fail on `p`. -/
theorem os.model.wp_stat_dirSW (op p : GoString) (R : Roots) (J : Ino) (dq : DFrac) (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗ osCallPerm (callKey R p) qc }}
      (App (App (Val (@! os.modelStat)) (Val #op)) (Val #p))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R p dq J ∗
        osCallPerm (callKey R p) qc ∗
        ((∃ (fs : Loc) (sz : w64), ⌜err = interface.nil ∧
            fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
            os.ownFileStat fs sz) ∨
         ⌜err ≠ interface.nil ∧ ¬ FsNoErrAt p⌝) }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm⟩
  imod osLogLb_0 with #Hlb
  try unfold os.model.stat
  unfold os.model.arbitraryMode
  icases osPathS_pathIn_keep R p dq J $$ Hp with ⟨%hpin, Hp⟩
  try wp_auto
  wp_stub os.fsPathKind.impl
  wp_apply wp_osPathKindS R p hpin.2 CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi
    as %k %hk
  have hk2 : k ≠ W64 2 := by rcases hk with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  try wp_auto
  try rw [decide_eq_false hk2]
  try wp_auto
  iloeb as IH generalizing Hperm Hp HΦ
  try wp_auto
  wp_open_stub
  wp_apply wp_osCallBeginS R _ qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [show W64 0x80000 = flRO from rfl]
  -- PORT: which stub? (OpenDirSW)
  wp_apply wp_osOpenDirSW R p J dq t s0 qc CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hp Hk as %fd %e %hres %hw Hperm Hp Hfd
  by_cases he4 : e = W64 4
  · iclear Hfd
    rw [decide_eq_true he4]
    try wp_auto
    try rw [os.fileStat_ty_eq]
    iapply IH $$ Hperm Hp HΦ
  rw [decide_eq_false he4]
  try wp_auto
  by_cases he0 : e = W64 0
  · subst he0
    ihave Hfd := Hfd $$ %rfl
    rw [decide_eq_true rfl]
    try wp_auto
    try wp_auto
    wp_stub os.fsFdKind.impl
    wp_apply wp_osFdKindDirS fd J .idle CoPset.subseteq_top $$ Hos Hfd as Hfd
    wp_apply internal.gomodel.wp_ChooseUint64 as %sz -
    iapply wp_fupd
    try wp_auto
    wp_stub os.fsDirClose.impl
    wp_apply wp_osDirCloseS fd J .idle CoPset.subseteq_top $$ Hos Hfd as %e2
    iStructNamed fs
    try wp_auto
    wp_apply filepathlite.Base.wp_lex as %nm _
    try wp_auto
    wp_apply internal.gomodel.wp_ChooseUint64 as %x -
    ipersist name
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
    isplitl []
    · iexists _; iassumption
    iexists _
    iassumption
  · iclear Hfd
    rw [decide_eq_false he0]
    try wp_auto
    wp_apply os.wp_modelErrno
    try wp_auto
    wp_apply os.wp_modelPathError
    iapply HΦ
    iframe
    iright
    ipureintro
    refine ⟨(fun hc => by cases hc), fun hne => ?_⟩
    rcases hw hne with h0 | h4
    · exact he0 h0
    · exact he4 h4
/-- `model.stat(op, d/b)` of the regular file `i` (a fraction of a claim on names containing `b`; no
`OsMeta`): a `fileStat` of some size, or an error only when the file system can fail on `d/b`. -/
theorem os.model.wp_stat_fileAnySW (op d b : GoString) (R : Roots) (j i : Ino) (N : NameSet)
    (dq dqn : DFrac) (h : NamesH) (qc : Qp) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc }}
      (App (App (Val (@! os.modelStat)) (Val #op)) (Val #(child d b)))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R d dq j ∗
        osNames j N dqn h ∗ osCallPerm (callKey R d) qc ∗
        ((∃ (fs : Loc) (sz : w64), ⌜err = interface.nil ∧
            fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
            os.ownFileStat fs sz) ∨
         ⌜err ≠ interface.nil ∧ ¬ FsNoErrAt (child d b)⌝) }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  imod osLogLb_0 with #Hlb
  try unfold os.model.stat
  unfold os.model.arbitraryMode
  icases osPathS_pathIn_keep R d dq j $$ Hp with ⟨%hpin, Hp⟩
  try wp_auto
  wp_stub os.fsPathKind.impl
  wp_apply wp_osPathKindS R (child d b) (pathIn_child hpin.2 hb) CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi as %k %hk
  have hk2 : k ≠ W64 2 := by rcases hk with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  try wp_auto
  try rw [decide_eq_false hk2]
  try wp_auto
  iloeb as IH generalizing Hperm Hp Hn HΦ
  icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  try wp_auto
  wp_open_stub
  wp_apply wp_osCallBeginS R _ qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  -- PORT: which stub? (OpenFileSW)
  wp_apply wp_osOpenFileSW R d b j i N dq dqn h t s0 qc (W64 0x80000)
    (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) hb hN hi
    CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk
    as %fd %e %hres %hw Hperm Hp Hn Hfd
  by_cases he4 : e = W64 4
  · iclear Hfd
    rw [decide_eq_true he4]
    try wp_auto
    try rw [os.fileStat_ty_eq]
    iapply IH $$ Hperm Hp Hn HΦ
  rw [decide_eq_false he4]
  try wp_auto
  by_cases he0 : e = W64 0
  · subst he0
    try wp_auto
    rw [if_pos (show W64 0 = (0 : w64) from rfl)]
    try wp_auto
    wp_stub os.fsFdKind.impl
    wp_apply wp_osFdKind fd (DFrac.own 1) _ CoPset.subseteq_top $$ Hos Hfd as Hfd
    try wp_auto
    wp_stub os.fsFstat.impl
    wp_apply wp_osFstatAnyW (GF := GF) fd (DFrac.own 1) (openFd i (W64 0x80000)) CoPset.subseteq_top
      $$ Hos Hfd as %sz %ez %hz Hfd
    try wp_auto
    wp_stub os.fsClose.impl
    wp_apply wp_osClose fd (openFd i (W64 0x80000)) CoPset.subseteq_top $$ [Hos Hfd] as %e2 -
    · iframe Hos Hfd; iapply lockToks_unlocked <;> rfl
    by_cases hz4 : ez = W64 4
    · rw [decide_eq_true hz4]
      try wp_auto
      try rw [os.fileStat_ty_eq]
      iapply IH $$ Hperm Hp Hn HΦ
    rw [decide_eq_false hz4]
    try wp_auto
    by_cases hz0 : ez = W64 0
    · subst hz0
      try rw [decide_eq_true rfl]
      iapply wp_fupd
      try wp_auto
      iStructNamed fs
      try wp_auto
      wp_apply filepathlite.Base.wp_lex as %nm _
      try wp_auto
      wp_apply internal.gomodel.wp_ChooseUint64 as %x -
      ipersist name
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
      isplitl []
      · iexists _; iassumption
      iexists _
      iassumption
    · rw [decide_eq_false (show ez ≠ W64 0 from hz0)]
      try wp_auto
      wp_apply os.wp_modelErrno
      try wp_auto
      wp_apply os.wp_modelPathError
      iapply HΦ
      iframe
      iright
      ipureintro
      exact ⟨(fun hc => by cases hc), fun hne => hz0 (hz (FsNoErrOn.mono hne.1 (fun _ h => h.elim)))⟩
  · iclear Hfd
    rw [decide_eq_false he0]
    try wp_auto
    wp_apply os.wp_modelErrno
    try wp_auto
    wp_apply os.wp_modelPathError
    iapply HΦ
    iframe
    iright
    ipureintro
    refine ⟨(fun hc => by cases hc), fun hne => ?_⟩
    rcases hw he0 with h4 | hn
    · exact he4 h4
    · exact hn hne

/-- `os.Stat(p)` of the directory `J` (a spine to it), an error only when the file system can fail
on `p`. -/
theorem os.Stat.wp_dirSW (p : GoString) (R : Roots) (J : Ino) (dq : DFrac) (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗ osCallPerm (callKey R p) qc }}
      (App (Val (@! os.Stat)) (Val #p))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R p dq J ∗
        osCallPerm (callKey R p) qc ∗
        ((∃ (fs : Loc) (sz : w64), ⌜err = interface.nil ∧
            fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
            os.ownFileStat fs sz) ∨
         ⌜err ≠ interface.nil ∧ ¬ FsNoErrAt p⌝) }} := by
  wp_start as Hpre
  wp_apply os.model.wp_stat_dirSW $$ Hpre
  iexact HΦ

/-- `os.Stat(d/b)` of the regular file `i` (no `OsMeta`), an error only when the file system can fail
on `d/b`. -/
theorem os.Stat.wp_fileAnySW (d b : GoString) (R : Roots) (j i : Ino) (N : NameSet)
    (dq dqn : DFrac) (h : NamesH) (qc : Qp) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc }}
      (App (Val (@! os.Stat)) (Val #(child d b)))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R d dq j ∗
        osNames j N dqn h ∗ osCallPerm (callKey R d) qc ∗
        ((∃ (fs : Loc) (sz : w64), ⌜err = interface.nil ∧
            fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
            os.ownFileStat fs sz) ∨
         ⌜err ≠ interface.nil ∧ ¬ FsNoErrAt (child d b)⌝) }} := by
  wp_start as Hpre
  wp_apply os.model.wp_stat_fileAnySW _ d b R j i N dq dqn h qc hb hN hi $$ Hpre
  iexact HΦ

end proof

end EtcdGrove
end Perennial

end
