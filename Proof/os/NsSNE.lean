/-
`os.OpenFile`/`os.Open` read-only of a directory in the tree's shared mode, **with no error**: where the
file system cannot fail on the path (`FsNoErrOn (· = p)`, the premises `NoIoErr`/`NoMapLockErr` covering
it) and the path fits (`PathFits p`), `open(2)` fails only with `EINTR` (`wp_osOpenDirSNE`), which
`OpenFile` retries, so it returns the directory's fd and `nil`. `NsSOk.lean`'s `wp_dirSOk` with the
error case refuted. Lean-first (no Rocq counterpart).
-/
module

public import Proof.os.NsS
public import GooseLang.Ext.Fs.NoErrSpecsOpenDir
public import GooseLang.Ext.Fs.FsNoErr

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

/-- **`os.OpenFile(p, O_RDONLY, perm)` of the directory `j`, with no error** (see the file header). -/
theorem os.OpenFile.wp_dirSNE (p : GoString) (perm : w32) (R : Roots) (j : Ino) (dq : DFrac)
    (qc : Qp) (hne : FsNoErrOn (· = p)) (hfit : PathFits p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq j ∗ osCallPerm (callKey R p) qc }}
      (App (App (App (Val (@! os.OpenFile)) (Val #p)) (Val #(W64 0))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R p dq j ∗ osCallPerm (callKey R p) qc ∗
        ∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗ osDirFdS fd j .idle }} := by
  obtain ⟨Sio, -, h1, h2, hpS⟩ := hne
  haveI := h1; haveI := h2
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  imod osLogLb_0 with #Hlb
  wp_for_bind
  iloeb as IH generalizing Hperm Hp HΦ
  wp_for_step
  try wp_auto
  wp_open_stub
  wp_apply wp_osCallBeginS R _ qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [show (W64 0 ||| W64 524288) = flRO from by decide]
  (try wp_auto)
  wp_apply wp_osOpenDirSNE Sio R p j dq t s0 qc ⟨hpS _ rfl, hfit⟩ CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi Hp Hk as %fd %e %hres Hperm Hp Hfd
  by_cases he0 : e = W64 0
  · subst he0
    ihave Hfd := Hfd $$ %rfl
    rw [decide_eq_true rfl]
    try wp_auto
    os_newfile
    wp_for_post_core
    iapply wp_fupd
    try wp_auto
    ipersist name
    ipersist f
    ipersist nonblock
    ipersist appendMode
    imodintro
    iapply HΦ
    iframe Hp Hperm
    iexists fd
    iframe
    isplitr
    · ipureintro; rfl
    unfold os.ownFile
    iexists _
    iframe
    (repeat' isplitl []) <;> iassumption
  · iclear Hfd
    rw [decide_eq_false he0]
    try wp_auto
    have he4 : e = W64 4 := by
      rcases hres with ⟨h0, -⟩ | ⟨-, -, h4⟩
      · exact absurd h0 he0
      · exact h4.trans (by decide)
    rw [decide_eq_true he4]
    try wp_auto
    try rw [os.file_ty_eq]
    try rw [os.File_ty_eq]
    wp_for_post
    inext
    iapply IH $$ Hperm Hp HΦ [$] [$] [$] [$] [$]

/-- **`os.Open(p)` of the directory `j`, with no error**: `OpenFile(p, O_RDONLY, 0)`. -/
theorem os.Open.wp_dirSNE (p : GoString) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp)
    (hne : FsNoErrOn (· = p)) (hfit : PathFits p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq j ∗ osCallPerm (callKey R p) qc }}
      (App (Val (@! os.Open)) (Val #p))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R p dq j ∗ osCallPerm (callKey R p) qc ∗
        ∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗ osDirFdS fd j .idle }} := by
  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm⟩
  try wp_auto
  wp_apply os.OpenFile.wp_dirSNE p (W32 0) R j dq qc hne hfit $$ [Hinv Hsi Hp Hperm] as %f %err Hr
  · iframe; (repeat' isplitl []) <;> iassumption
  iapply HΦ
  iexact Hr

end proof

end EtcdGrove
end Perennial
