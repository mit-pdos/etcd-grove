/-
Specs of `os`'s trusted models at a strict ancestor of a root (2026-11-13,
`notes/wal-fsext-models-review.md`, "Above-root Stat/Open"), in the tree's shared mode:
`model.stat` (`Stat`/`Lstat`: no extension step but the query `PathKind`), `OpenFile`/`Open`
read-only (an outside fd, `osOutFd`, or an error), and `Sync`/`Close` of such an fd. Untrusted.
-/
module

public import Proof.os.IgnoringEINTR
public import Perennial.Proof.internal.gomodel.Link
public import Proof.os.NsS
public import Proof.os.PathKindS
public import Proof.os.PathParent
public import Spec.os.StatAbove
public import Proof.os.StatAboveS

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

/-- `os.OpenFile(p, O_RDONLY, perm)` of a strict ancestor of a root: an outside fd, or an error. -/
theorem os.OpenFile.wp_aboveS (p : GoString) (perm : w32) (R : Roots) (hp : RootsAbove R p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osAboveInv }}
      (App (App (App (Val (@! os.OpenFile)) (Val #p)) (Val #(W64 0))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗ osOutFd fd) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝ ∗ fmtErrorOk err) }} := by
  wp_start as ⟨#Hos, #Hsi, #Hab⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  imod osLogLb_0 with #Hlb
  wp_for_bind
  iloeb as IH generalizing HΦ
  wp_for_step
  try wp_auto
  wp_open_stub
  wp_apply wp_osCallBeginAboveS R _ hp 0 CoPset.subseteq_top CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hab Hlb as %t %s0 %qc %hs Hk Hls
  iclear Hls
  rw [show (W64 0 ||| W64 524288) = flRO from by decide]
  (try wp_auto)
  wp_apply wp_osOpenAboveS R p hp t s0 qc CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hk as %fd %e %hres - Hfd
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
    iframe
    ileft
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
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      try wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      wp_for_post
      inext
      iapply IH $$ HΦ [$] [$] [$] [$] [$]
    · rw [decide_eq_false he4]
      try wp_auto
      wp_apply os.wp_modelErrno
      try wp_auto
      wp_apply os.wp_modelPathError_ok _ _ e he0 $$ Hsys as %pe #Hok
      try wp_auto
      wp_for_post
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
      iexact Hok

/-- `os.Open(p)` of a strict ancestor of a root: `OpenFile(p, O_RDONLY, 0)`. -/
theorem os.Open.wp_aboveS (p : GoString) (R : Roots) (hp : RootsAbove R p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osAboveInv }}
      (App (Val (@! os.Open)) (Val #p))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗ osOutFd fd) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝ ∗ fmtErrorOk err) }} := by
  wp_start as ⟨#Hinv, #Hsi, #Hab⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  try wp_auto
  wp_apply os.OpenFile.wp_aboveS p (W32 0) R hp $$ [] as %f %err Hr
  · isplitl [] <;> try isplitl []
    all_goals iassumption
  iapply HΦ
  iexact Hr

/-- `f.Sync()` of an outside fd: any error; the fd kept. -/
theorem os.File.Sync.wp_outS (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osOutFd fd }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
    {{ (err : GoInterface), RET #err; fmtErrorOkOrNil err ∗ os.ownFile f fd name dqf ∗ osOutFd fd }} := by
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hnb, #Hap, #Hsys⟩, Hosfd⟩
  ihave #Hf2 := Hf
  iStructNamed Hf2
  try wp_auto
  try wp_auto
  wp_stub os.fsFdKind.impl
  wp_apply wp_osFdKindOut fd CoPset.subseteq_top $$ Hinv Hosfd as Hosfd
  try wp_auto
  wp_for_bind
  iloeb as IH generalizing Hosfd HΦ
  wp_for_step
  try wp_auto
  wp_stub os.fsOutSync.impl
  wp_apply wp_osOutSync fd CoPset.subseteq_top $$ Hinv Hosfd as %e Hosfd
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    try wp_auto
    wp_for_post
    inext
    iapply IH $$ Hosfd HΦ Hfd [$] [$] [$] [$]
  rw [decide_eq_false he4]
  try wp_auto
  by_cases he : e = W64 0
  · subst he
    rw [show decide ((W64 0 : w64) = W64 0) = true from decide_eq_true rfl]
    simp only [Bool.not_true]
    try wp_auto
    wp_for_post
    iapply HΦ
    isplitr
    · iapply fmtErrorOkOrNil_nil
    iframe
    (repeat' isplitl []) <;> iassumption
  · simp only [decide_eq_false he, Bool.not_false]
    try wp_auto
    wp_apply os.wp_wrapErrno_ok _ inner name e he $$ Hn Hsys as %pe #Hpe
    wp_for_post
    iapply HΦ
    isplitr
    · iapply fmtErrorOkOrNil_of $$ Hpe
    iframe
    (repeat' isplitl []) <;> iassumption

/-- `f.Close()` of an outside fd: any error; the fd gone. -/
theorem os.File.Close.wp_outS (f : Loc) (fd : w64) (name : GoString) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name (DFrac.own 1) ∗ osOutFd fd }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #()))
    {{ (err : GoInterface), RET #err; fmtErrorOkOrNil err }} := by
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hnb, #Hap, #Hsys⟩, Hosfd⟩
  ihave #Hf2 := Hf
  iStructNamed Hf2
  ihave %hnn := typedPointsto_not_null _ _ _ $$ Hf
  try wp_auto
  rw [decide_eq_false hnn]
  try wp_auto
  ihave %hfd0 := osOutFd_nonneg _ $$ Hosfd
  rw [decide_eq_false (show fd ≠ W64 (-1) by rintro rfl; exact absurd hfd0 (by decide))]
  try wp_auto
  try wp_auto
  wp_stub os.fsFdKind.impl
  wp_apply wp_osFdKindOut fd CoPset.subseteq_top $$ Hinv Hosfd as Hosfd
  try wp_auto
  try wp_auto
  wp_stub os.fsOutClose.impl
  wp_apply wp_osOutClose fd CoPset.subseteq_top $$ Hinv Hosfd as %e
  by_cases he : e = W64 0
  · rw [decide_eq_true he]
    try wp_auto
    iapply HΦ
    iapply fmtErrorOkOrNil_nil
  · rw [decide_eq_false he]
    try wp_auto
    wp_apply os.wp_wrapErrno_ok _ inner name e he $$ Hn Hsys as %pe #Hpe
    try wp_auto
    iapply HΦ
    iapply fmtErrorOkOrNil_of $$ Hpe

end proof

end EtcdGrove
end Perennial
