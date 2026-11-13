/-
Specs of `os`'s trusted models at a strict ancestor of a root (2026-11-13,
`notes/wal-fsext-models-review.md`, "Above-root Stat/Open"), in the tree's shared mode:
`model.stat` (`Stat`/`Lstat`: no extension step but the query `PathKind`), `OpenFile`/`Open`
read-only (an outside fd, `osOutFd`, or an error), and `Sync`/`Close` of such an fd. Untrusted.
-/
module

public import LinuxFs.Proof.os.NsS
public import LinuxFs.Proof.os.PathKindS
public import LinuxFs.Spec.os.StatAbove

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- `ancPath l ++ "/"` for non-empty `l`, followed by more components, is a prefix of the path. -/
theorem os.ancPath_prefix (a : List GoString) (c : GoString) (rest : List GoString) (ha : a ≠ []) :
    (os.ancPath a ++ [slashB]).IsPrefix (joinPath [] (a ++ c :: rest)) := by
  unfold os.ancPath
  rw [if_neg ha, joinPath_append]
  exact prefix_joinPath_cons _ _ _

/-- A strict ancestor of a root (`os.AboveRoot`, as the specs state it) is one of the extension's
(`RootsAbove`). -/
theorem os.aboveRoot_rootsAbove {R : Roots} {p : GoString} (h : os.AboveRoot R p) :
    RootsAbove R p := by
  obtain ⟨rcs, j0, k, hm, hk, rfl⟩ := h
  by_cases hk0 : k = 0
  · subst hk0; left; simp [os.ancPath]
  right
  have hne : rcs.take k ≠ [] := by
    intro h; rw [List.take_eq_nil_iff] at h
    rcases h with h | h
    · exact hk0 h
    · subst h; simp at hk
  refine ⟨?_, (joinPath [] rcs, j0), hm, ?_⟩
  · unfold os.ancPath; rw [if_neg hne]
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
    rw [hcs]; simp [joinPath]
  · have hd : rcs.drop k ≠ [] := by simp; omega
    obtain ⟨c, rest, hcr⟩ := List.exists_cons_of_ne_nil hd
    have := os.ancPath_prefix (rcs.take k) c rest hne
    rwa [← hcr, List.take_append_drop] at this

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [go.BasicIntoValInj]

variable [os.fileStat.FieldAssumptions] in
/-- `model.stat(op, p)` of a strict ancestor of a root: some answer, nothing changed. -/
theorem os.model.wp_stat_aboveS (op p : GoString) (R : Roots) (hp : RootsAbove R p) :
    {{ osInv (GF := GF) ∗ osSharedInv R }}
      (App (App (Val os.model.stat) (Val #op)) (Val #p))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); True }} := by
  wp_start as ⟨#Hos, #Hsi⟩
  try unfold os.model.stat
  unfold os.model.statAbove os.model.arbitraryMode
  rw [os.fileStat_ty_eq]
  wp_apply wp_osPathKindAboveS R p hp CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi
  try wp_auto
  wp_apply wp_ArbitraryInt as %x _
  by_cases hx : x = W64 0
  · subst hx
    try wp_auto
    iStructNamed fs
    wp_apply wp_ArbitraryInt as %sz _
    try wp_auto
    wp_apply wp_ArbitraryInt as %y _
    by_cases hy : y = W64 0
    · subst hy
      try wp_auto
      wp_apply wp_ArbitraryInt as %z _
      try wp_auto
      iapply HΦ $$ %_ %_
      itrivial
    · rw [decide_eq_false hy]
      try wp_auto
      wp_apply wp_ArbitraryInt as %z _
      try wp_auto
      iapply HΦ $$ %_ %_
      itrivial
  · rw [decide_eq_false hx]
    try wp_auto
    wp_apply wp_ArbitraryInt as %m _
    try wp_auto
    unfold os.model.pathError
    by_cases hm : m = W64 0
    · subst hm
      try wp_auto
      wp_apply wp_errno
      try wp_auto
      iapply HΦ $$ %_ %_
      itrivial
    · rw [decide_eq_false hm]
      try wp_auto
      wp_apply wp_errno
      try wp_auto
      iapply HΦ $$ %_ %_
      itrivial

variable [os.file.FieldAssumptions] in
/-- `os.OpenFile(p, O_RDONLY, perm)` of a strict ancestor of a root: an outside fd, or an error. -/
theorem os.OpenFile.wp_aboveS (p : GoString) (perm : w32) (R : Roots) (hp : RootsAbove R p)
    (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osCallPerm qc }}
      (App (App (App (Val (@! os.OpenFile)) (Val #p)) (Val #(W64 0))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osCallPerm qc ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗ osOutFd fd) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝) }} := by
  wp_start as ⟨#Hos, #Hsi, Hperm⟩
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm HΦ
  wp_apply wp_osCallBeginS R qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [os.file_ty_eq, os.File_ty_eq]
  rw [show (W64 0 ||| W64 524288) = flRO from by decide]
  (try wp_auto)
  wp_apply wp_osOpenAboveS R p hp t s0 qc CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hk as %fd %e %hres Hperm Hfd
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
      iapply IH $$ Hperm HΦ
    · rw [decide_eq_false he4]
      wp_auto
      unfold os.model.pathError
      wp_apply wp_errno
      iapply HΦ
      iframe
      iright
      ipureintro; exact ⟨(fun h => by cases h), rfl⟩

variable [os.file.FieldAssumptions] in
/-- `os.Open(p)` of a strict ancestor of a root: `OpenFile(p, O_RDONLY, 0)`. -/
theorem os.Open.wp_aboveS (p : GoString) (R : Roots) (hp : RootsAbove R p) (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osCallPerm qc }}
      (App (Val (@! os.Open)) (Val #p))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osCallPerm qc ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗ osOutFd fd) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝) }} := by
  wp_start as ⟨#Hinv, #Hsi, Hperm⟩
  wp_auto
  wp_apply os.OpenFile.wp_aboveS p (W32 0) R hp qc $$ [Hinv Hsi Hperm] as %f %err Hr
  · iframe; isplitl [] <;> iassumption
  iapply HΦ
  iexact Hr

/-- `f.Sync()` of an outside fd: any error; the fd kept. -/
theorem os.File.Sync.wp_outS (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osOutFd fd }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
    {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osOutFd fd }} := by
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  wp_apply wp_osFdKindOut fd CoPset.subseteq_top $$ Hinv Hosfd as Hosfd
  try wp_auto
  iloeb as IH generalizing Hosfd HΦ
  wp_apply wp_osOutSync fd CoPset.subseteq_top $$ Hinv Hosfd as %e Hosfd
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    iapply IH $$ Hosfd HΦ Hfd
  rw [decide_eq_false he4]
  wp_auto
  by_cases he : e = W64 0
  · subst he
    rw [show decide ((W64 0 : w64) = W64 0) = true from decide_eq_true rfl]
    simp only [Bool.not_true]
    wp_auto
    iapply HΦ
    iframe
    isplitl [] <;> iassumption
  · simp only [decide_eq_false he, Bool.not_false]
    wp_auto
    wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
    iapply HΦ
    iframe
    isplitl [] <;> iassumption

/-- `f.Close()` of an outside fd: any error; the fd gone. -/
theorem os.File.Close.wp_outS (f : Loc) (fd : w64) (name : GoString) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name (DFrac.own 1) ∗ osOutFd fd }}
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
  wp_apply wp_osFdKindOut fd CoPset.subseteq_top $$ Hinv Hosfd as Hosfd
  try wp_auto
  wp_apply wp_osOutClose fd CoPset.subseteq_top $$ Hinv Hosfd as %e
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

end proof

end EtcdGrove
end Perennial
