/-
`os.Stat` and `os.Lstat` (the Go model's `modelStat`) of a strict ancestor of a root (`RootsAbove`,
`PathKind` 2): `modelStatAbove`, no extension step but the query `PathKind`; a fresh `*fileStat`
(`os.ownFileStat`: Go's `MkdirAll` calls `IsDir` on it) with a nil error, or a non-nil error.
Untrusted.
-/
module

public import Proof.os.IgnoringEINTR
public import Proof.internal.gomodel.LocalChoose
public import Proof.os.ModelMode
public import Proof.os.ErrorOk
public import Proof.internal.filepathlite.Lexical
public import Proof.os.PathKindS
public import Proof.os.PathParent
public import Spec.os.StatAbove

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

/-- `modelStatAbove(op, p)`: a fresh `*fileStat` and a nil error, or a non-nil error. -/
theorem os.model.wp_statAbove (op p : GoString) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! os.modelStatAbove)) (Val #op)) (Val #p))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err);
        (∃ (fs : Loc) (sz : w64), ⌜err = interface.nil ∧
            fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
            os.ownFileStat fs sz) ∨
         ⌜err ≠ interface.nil⌝ }} := by
  wp_start as -
  try wp_auto
  wp_apply internal.gomodel.Choose.wp_local as %c -
  cases c
  · try wp_auto
    wp_apply internal.gomodel.ChooseUint64.wp_local as %x -
    try wp_auto
    by_cases hx : x = W64 0
    · subst hx
      try wp_auto
      wp_apply os.wp_modelErrno
      try wp_auto
      wp_apply os.wp_modelPathError
      iintro %pe
      try wp_auto
      iapply HΦ
      iright
      ipureintro; intro hc; cases hc
    · try rw [decide_eq_false hx]
      try wp_auto
      wp_apply os.wp_modelErrno
      try wp_auto
      wp_apply os.wp_modelPathError
      iintro %pe
      try wp_auto
      iapply HΦ
      iright
      ipureintro; intro hc; cases hc
  · try simp only [os.ModeSymlink, os.ModeDir]
    iapply wp_fupd
    try wp_auto
    iStructNamed «$r0»
    try wp_auto
    wp_apply filepathlite.Base.wp_lex as %nm _
    try wp_auto
    wp_apply internal.gomodel.ChooseUint64.wp_local as %sz -
    try simp only [os.ModeSymlink, os.ModeDir]
    try wp_auto
    wp_apply internal.gomodel.Choose.wp_local as %d -
    cases d
    all_goals
      try wp_auto
      wp_apply os.wp_modelMode as %x
      try wp_auto
      ipersist name
      ipersist size
      ipersist mode
      imodintro
      iapply HΦ
      ileft
      iexists «$r0_ptr», _
      unfold os.ownFileStat
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitl []
      · iassumption
      isplitl []
      · iexists _; iassumption
      iexists _
      iassumption

/-- `model.stat(op, p)` of a strict ancestor of a root: a fresh `*fileStat` and a nil error, or a
non-nil error; nothing changed. -/
theorem os.model.wp_stat_aboveS (op p : GoString) (R : Roots) (hp : RootsAbove R p) :
    {{ osInv (GF := GF) ∗ osSharedInv R }}
      (App (App (Val (@! os.modelStat)) (Val #op)) (Val #p))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err);
        (∃ (fs : Loc) (sz : w64), ⌜err = interface.nil ∧
            fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
            os.ownFileStat fs sz) ∨
         ⌜err ≠ interface.nil⌝ }} := by
  wp_start as ⟨#Hos, #Hsi⟩
  try wp_auto
  wp_stub os.fsPathKind.impl
  wp_apply wp_osPathKindAboveS R p hp CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi
  try wp_auto
  wp_apply os.model.wp_statAbove as %fi %err Hr
  try wp_auto
  iapply HΦ
  iexact Hr

/-- `os.Stat(p)` of a strict ancestor of a root, as `os.model.wp_stat_aboveS`. -/
theorem os.Stat.wp_aboveS (p : GoString) (R : Roots) (hp : RootsAbove R p) :
    {{ osInv (GF := GF) ∗ osSharedInv R }}
      (App (Val (@! os.Stat)) (Val #p))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err);
        (∃ (fs : Loc) (sz : w64), ⌜err = interface.nil ∧
            fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
            os.ownFileStat fs sz) ∨
         ⌜err ≠ interface.nil⌝ }} := by
  wp_start as Hpre
  try wp_auto
  wp_apply os.model.wp_stat_aboveS _ p R hp $$ Hpre as %fi %err Hpost
  try wp_auto
  iapply HΦ
  iexact Hpost

/-- `os.Lstat(p)` of a strict ancestor of a root, as `os.model.wp_stat_aboveS`. -/
theorem os.Lstat.wp_aboveS (p : GoString) (R : Roots) (hp : RootsAbove R p) :
    {{ osInv (GF := GF) ∗ osSharedInv R }}
      (App (Val (@! os.Lstat)) (Val #p))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err);
        (∃ (fs : Loc) (sz : w64), ⌜err = interface.nil ∧
            fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
            os.ownFileStat fs sz) ∨
         ⌜err ≠ interface.nil⌝ }} := by
  wp_start as Hpre
  try wp_auto
  wp_apply os.model.wp_stat_aboveS _ p R hp $$ Hpre as %fi %err Hpost
  try wp_auto
  iapply HΦ
  iexact Hpost

end proof

end EtcdGrove
end Perennial
