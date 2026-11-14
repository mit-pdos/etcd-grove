/-
Specs of `os`'s trusted models (`TrustedCode/os.lean`) on the directory tree: `OpenFile`
read-only of a directory and of a file, `(*File).Readdirnames(-1)`, and a directory fd's `Sync` and
`Close`. Over the extension's tree specs (`GooseLang/Ext/Fs/TreeSpecsOpen.lean`,
`TreeSpecsDirFd.lean`): each open attempt a `CallBegin` taking the fraction `q` of the caller's
history to the call, which a directory fd keeps (its read's view) and `Close` gives back.
Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.OpenFile
public import LinuxFs.Proof.os.File__Close

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

/-- `os.OpenFile(p, O_RDONLY, perm)` of a directory `j` of the tree, with the fractions `q1 + q` of
the history: a directory fd, not read, holding `q` (its view of `j` the history's), `q1` back; or
an error, `q1 + q` back. -/
theorem os.OpenFile.wp_dir (p : GoString) (perm : w32) (q1 q : Qp) (R : Roots) (V : Hist) (j : Ino)
    (hl : lookupH R V p = some (.dir j)) :
    {{ osInv (GF := GF) ∗ osTree (GF := GF) (DFrac.own (q1 + q)) R V }}
      (App (App (App (Val (@! os.OpenFile)) (Val #p)) (Val #(W64 0))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗
            osTree (DFrac.own q1) R V ∗ osDirFd fd (DFrac.own 1) (j, .idle (dview V j) q)) ∨
         (⌜err ≠ interface.nil ∧ f = null⌝ ∗ osTree (DFrac.own (q1 + q)) R V)) }} := by
  wp_start as ⟨#Hinv, Hh⟩
  iloeb as IH generalizing Hh HΦ
  wp_apply wp_osCallBegin R V q1 q CoPset.subseteq_top $$ Hinv Hh as %t Hh Hk
  rw [os.file_ty_eq, os.File_ty_eq]
  rw [show (W64 0 ||| W64 524288) = flRO from by decide]
  (try wp_auto)
  wp_apply wp_osOpenDir p R V q1 q t _ j hl CoPset.subseteq_top $$ Hinv Hh Hk as %fd %e %hres Hr
  by_cases he0 : e = W64 0
  · subst he0
    rw [if_pos (show W64 0 = (0 : w64) from rfl)]
    icases Hr with ⟨Hh, Hfd⟩
    rw [decide_eq_true rfl]
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    iapply HΦ
    ileft
    iexists fd
    iframe Hfd Hh
    isplitr
    · ipureintro; rfl
    unfold os.ownFile
    iexists inner_ptr
    iframe
    isplitl [] <;> iassumption
  · rw [if_neg (show ¬ e = (0 : w64) from he0)]
    rw [decide_eq_false he0]
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      iapply IH $$ Hr HΦ
    · rw [decide_eq_false he4]
      wp_auto
      unfold os.model.pathError
      wp_apply wp_errno
      iapply HΦ
      iright
      iframe Hr
      ipureintro; exact ⟨(fun h => by cases h), rfl⟩

/-- `os.Open(p)` of a directory of the tree: `OpenFile(p, O_RDONLY, 0)`. -/
theorem os.Open.wp_dir (p : GoString) (q1 q : Qp) (R : Roots) (V : Hist) (j : Ino)
    (hl : lookupH R V p = some (.dir j)) :
    {{ osInv (GF := GF) ∗ osTree (GF := GF) (DFrac.own (q1 + q)) R V }}
      (App (Val (@! os.Open)) (Val #p))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗
            osTree (DFrac.own q1) R V ∗ osDirFd fd (DFrac.own 1) (j, .idle (dview V j) q)) ∨
         (⌜err ≠ interface.nil ∧ f = null⌝ ∗ osTree (DFrac.own (q1 + q)) R V)) }} := by
  wp_start as ⟨#Hinv, Hh⟩
  wp_auto
  wp_apply os.OpenFile.wp_dir p (W32 0) q1 q R V j hl $$ [Hinv Hh] as %f %err Hr
  · iframe; iexact Hinv
  iapply HΦ
  iexact Hr

/-- `f.Close()` of a directory fd: any error; the fd gone, and what its read held back. -/
theorem os.File.Close.wp_dir (f : Loc) (fd : w64) (name : GoString) (x : Ino × DirPh) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name (DFrac.own 1) ∗
        osDirFd (GF := GF) fd (DFrac.own 1) x }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #()))
    {{ (err : GoInterface), RET #err; rdBack (GF := GF) x }} := by
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  ihave %hnn := typedPointsto_not_null _ _ _ $$ Hf
  rw [decide_eq_false hnn]
  wp_auto
  wp_apply wp_osFdKindDir fd (DFrac.own 1) x CoPset.subseteq_top $$ Hinv Hosfd as Hosfd
  wp_apply wp_osDirClose fd x CoPset.subseteq_top $$ Hinv Hosfd as %e Hb
  by_cases he : e = W64 0
  · rw [decide_eq_true he]
    wp_auto
    iapply HΦ
    iexact Hb
  · rw [decide_eq_false he]
    wp_auto
    wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
    iapply HΦ
    iexact Hb

/-- `f.Sync()` of a directory fd: any error, the fd as it was (`DirSync`, `EINTR` retried). -/
theorem os.File.Sync.wp_dir (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac)
    (x : Ino × DirPh) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osDirFd (GF := GF) fd dq x }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
    {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osDirFd fd dq x }} := by
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  wp_apply wp_osFdKindDir fd dq x CoPset.subseteq_top $$ Hinv Hosfd as Hosfd
  iloeb as IH generalizing Hosfd HΦ
  wp_apply wp_osDirSync fd dq x CoPset.subseteq_top $$ Hinv Hosfd as %e Hosfd
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

/-- `f.Readdirnames(n)`, `n ≤ 0`, of a directory fd not yet read, `g` its directory's view in
the history fraction it holds: every name of `g.now`, once each, the fd read; or an error. The
fraction stays with the fd either way (`Close` gives it back). -/
theorem os.File.Readdirnames.wp_dir (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac)
    (d : Ino) (q : Qp) (g : DirG) (n : w64) (hn : sint.Z n ≤ 0) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗
        osDirFd (GF := GF) fd (DFrac.own 1) (d, .idle g q) }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Readdirnames")) (Val #n))
    {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); os.ownFile f fd name dqf ∗
        ((∃ names : List GoString, ⌜err = interface.nil ∧ names.Nodup ∧
              ∀ b, b ∈ names ↔ (g.now !! b).isSome⌝ ∗ sl ↦* names ∗
            osDirFd fd (DFrac.own 1) (d, .done g q)) ∨
         (⌜err ≠ interface.nil⌝ ∗ ∃ rs, osDirFd fd (DFrac.own 1) (d, .reading rs g q))) }} := by
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd⟩
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
  ihave Hosfd : osDirFd fd (DFrac.own 1) (d, if fresh then .idle g q else .reading rs g q) $$ [Hosfd]
  · subst hfresh; simp only [↓reduceIte]; iexact Hosfd
  generalize hsl0 : slice.mk _ _ _ = sl0
  ihave Hsl : sl0 ↦* rs.reverse $$ [Hsl]
  · subst hrs; rw [List.reverse_nil]; iexact Hsl
  ihave Hp : ⌜(fresh = true → rs = []) ∧ rs.Nodup ∧ ∀ b ∈ rs, (g.now !! b).isSome⌝ $$ []
  · ipureintro; subst hrs; simp
  clear hfresh hrs hsl0
  wp_auto
  iloeb as IH generalizing %fresh %rs %sl0 Hp Hosfd Hsl Hcap
  icases Hp with %Hp
  obtain ⟨hfr, hnd, hin⟩ := Hp
  wp_apply wp_osDirReadStep fd d rs g q fresh hfr CoPset.subseteq_top $$ Hinv Hosfd as %v Hv
  icases Hv with (⟨%b, %hv, Hosfd⟩ | ⟨%hv, Hosfd⟩ | ⟨%e, %hv, Hosfd⟩)
  · obtain ⟨rfl, hb, hbr⟩ := hv
    wp_auto
    wp_apply_core wp_assume
    iintro %-
    wp_auto
    wp_apply wp_slice_literal (V := GoString) [b]
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl1] as %sl' ⟨Hsl, Hcap, -⟩
    iapply IH $$ %false %(b :: rs) %sl' [] [Hosfd] [Hsl] Hcap HΦ Hfd
    · ipureintro
      refine ⟨fun h => absurd h Bool.false_ne_true, List.nodup_cons.2 ⟨hbr, hnd⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hb
      · exact hin x hx
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
    refine ⟨rfl, List.pairwise_reverse.2 (hnd.imp fun h e => h e.symm), fun x => ?_⟩
    rw [List.mem_reverse]
    exact ⟨hin x, hall x⟩
  · obtain ⟨he, rfl⟩ := hv
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ %false %rs %sl0 [] [Hosfd] Hsl Hcap HΦ Hfd
      · ipureintro; exact ⟨fun h => absurd h Bool.false_ne_true, hnd, hin⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hosfd
    · rw [decide_eq_false he4]
      wp_auto
      rw [decide_eq_false (show ¬ e = W64 0 from he)]
      wp_auto
      wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
      iapply HΦ
      iframe
      isplitl []
      · isplitl [] <;> iassumption
      iright
      isplitr
      · ipureintro; intro h; cases h
      iexists rs
      iexact Hosfd

/-- `os.OpenFile(p, O_RDONLY, perm)` of a file `i` of the tree, with a fraction of the history,
which comes back: a read-only fd on `i`, or an error. -/
theorem os.OpenFile.wp_nsRO (p : GoString) (perm : w32) (q : Qp) (R : Roots) (V : Hist) (i : Ino)
    (hl : lookupH R V p = some (.file i)) :
    {{ osInv (GF := GF) ∗ osTree (GF := GF) (DFrac.own q) R V }}
      (App (App (App (Val (@! os.OpenFile)) (Val #p)) (Val #(W64 0))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osTree (DFrac.own q) R V ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗
            osFd fd (DFrac.own 1) ⟨i, true, false⟩) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝) }} := by
  wp_start as ⟨#Hinv, Hh⟩
  iloeb as IH generalizing Hh HΦ
  ihave Hh := (osTree_halves q R V).1 $$ Hh
  wp_apply wp_osCallBegin R V q.half q.half CoPset.subseteq_top $$ Hinv Hh as %t Hh Hk
  rw [os.file_ty_eq, os.File_ty_eq]
  rw [show (W64 0 ||| W64 524288) = flRO from by decide]
  (try wp_auto)
  wp_apply wp_osOpenFile p flRO R V q.half q.half t _ i flRO_ok (by decide) hl
    CoPset.subseteq_top $$ Hinv Hh Hk as %fd %e %hres Hh Hfd
  ihave Hh := (osTree_halves q R V).2 $$ Hh
  by_cases he0 : e = W64 0
  · subst he0
    rw [decide_eq_true rfl]
    rw [if_pos (show W64 0 = (0 : w64) from rfl),
      show openFd i flRO = ⟨i, true, false⟩ by simp [openFd, O_WRONLY, O_RDONLY]]
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    iapply HΦ
    iframe Hh
    ileft
    iexists fd
    iframe Hfd
    isplitr
    · ipureintro; rfl
    unfold os.ownFile
    iexists inner_ptr
    iframe
    isplitl [] <;> iassumption
  · rw [decide_eq_false he0, if_neg (show ¬ e = (0 : w64) from he0)]
    iclear Hfd
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      iapply IH $$ Hh HΦ
    · rw [decide_eq_false he4]
      wp_auto
      unfold os.model.pathError
      wp_apply wp_errno
      iapply HΦ
      iframe Hh
      iright
      ipureintro; exact ⟨(fun h => by cases h), rfl⟩

end proof

end EtcdGrove
end Perennial
