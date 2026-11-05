/-
Specs of `os`'s trusted models (`TrustedCode/os.lean`) on the namespace (`notes/walfs-ext-plan.md`):
`OpenFile` read-only of a directory and of a file of one, `(*File).Readdirnames(-1)`, and a
directory fd's `Sync` and `Close`. Over the extension's specs (`GooseLang/Ext/OsFs/NsSpecs*.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.os.OpenFile
public import Proof.os.File__Close
public import GooseLang.Ext.OsFs.CrashNs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj]

/-- `os.OpenFile(d, O_RDONLY, perm)` of a directory of the namespace: a directory fd, not read,
or an error. -/
theorem os.OpenFile.wp_dir (d : GoString) (perm : w32) (dq : DFrac) (g : DirG) :
    {{ osInv (GF := GF) ∗ osDir (GF := GF) d dq g }}
      (App (App (App (Val (@! os.OpenFile)) (Val #d)) (Val #(W64 0))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osDir d dq g ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd d (DFrac.own 1) ∗
            osDirFd fd (DFrac.own 1) (d, .idle)) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝) }} := by
  wp_start as ⟨#Hinv, Hd⟩
  iloeb as IH generalizing Hd HΦ
  wp_apply wp_osRegimeNs d d dq g (.inl rfl) CoPset.subseteq_top $$ Hinv Hd as Hd
  rw [os.file_ty_eq, os.File_ty_eq]
  rw [show (W64 0 ||| W64 524288) = flRO from by decide]
  wp_apply wp_osNsOpenDir d dq g CoPset.subseteq_top $$ Hinv Hd as %fd %e %hres Hd Hfd
  by_cases he0 : e = W64 0
  · subst he0
    rw [decide_eq_true rfl]
    rw [if_pos (show W64 0 = (0 : w64) from rfl)]
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    iapply HΦ
    iframe Hd
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
      iapply IH $$ Hd HΦ
    · rw [decide_eq_false he4]
      wp_auto
      unfold os.model.pathError
      wp_apply wp_errno
      iapply HΦ
      iframe Hd
      iright
      ipureintro; exact ⟨(fun h => by cases h), rfl⟩

/-- `os.Open(d)` of a directory of the namespace: `OpenFile(d, O_RDONLY, 0)`. -/
theorem os.Open.wp_dir (d : GoString) (dq : DFrac) (g : DirG) :
    {{ osInv (GF := GF) ∗ osDir (GF := GF) d dq g }}
      (App (Val (@! os.Open)) (Val #d))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osDir d dq g ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd d (DFrac.own 1) ∗
            osDirFd fd (DFrac.own 1) (d, .idle)) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝) }} := by
  wp_start as ⟨#Hinv, Hd⟩
  wp_auto
  wp_apply os.OpenFile.wp_dir d (W32 0) dq g $$ [Hinv Hd] as %f %err ⟨Hd, Hr⟩
  · iframe; iexact Hinv
  iapply HΦ
  iframe

/-- `f.Close()` of a directory fd: any error; the fd gone, and what its read held back. -/
theorem os.File.Close.wp_dir (f : Loc) (fd : w64) (name : GoString) (x : GoString × DirPh) :
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
    (x : GoString × DirPh) :
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

/-- `f.Readdirnames(n)`, `n ≤ 0`, of a directory fd not yet read, lending the read a fraction of
the directory's ghost entry `g`: every name of `g.now`, once each, the fd read and the fraction
back; or an error, the fraction with the fd (`Close` gives it back). -/
theorem os.File.Readdirnames.wp_dir (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac)
    (d : GoString) (q : Qp) (g : DirG) (n : w64) (hn : sint.Z n ≤ 0) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗
        osDirFd (GF := GF) fd (DFrac.own 1) (d, .idle) ∗ osDir (GF := GF) d (DFrac.own q) g }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Readdirnames")) (Val #n))
    {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); os.ownFile f fd name dqf ∗
        ((∃ names : List GoString, ⌜err = interface.nil ∧ names.Nodup ∧
              ∀ b, b ∈ names ↔ (g.now !! b).isSome⌝ ∗ sl ↦* names ∗
            osDirFd fd (DFrac.own 1) (d, .done) ∗ osDir d (DFrac.own q) g) ∨
         (⌜err ≠ interface.nil⌝ ∗ ∃ rs, osDirFd fd (DFrac.own 1) (d, .reading rs g q))) }} := by
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hd⟩
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
  ihave Hosfd : osDirFd fd (DFrac.own 1) (d, if fresh then .idle else .reading rs g q) $$ [Hosfd]
  · subst hfresh; simp only [↓reduceIte]; iexact Hosfd
  ihave Hd : (if fresh then osDir d (DFrac.own q) g else emp) $$ [Hd]
  · subst hfresh; simp only [↓reduceIte]; iexact Hd
  generalize hsl0 : slice.mk _ _ _ = sl0
  ihave Hsl : sl0 ↦* rs.reverse $$ [Hsl]
  · subst hrs; rw [List.reverse_nil]; iexact Hsl
  ihave Hp : ⌜(fresh = true → rs = []) ∧ rs.Nodup ∧ ∀ b ∈ rs, (g.now !! b).isSome⌝ $$ []
  · ipureintro; subst hrs; simp
  clear hfresh hrs hsl0
  wp_auto
  iloeb as IH generalizing %fresh %rs %sl0 Hp Hosfd Hd Hsl Hcap
  icases Hp with %Hp
  obtain ⟨hfr, hnd, hin⟩ := Hp
  wp_apply wp_osDirReadStep fd d rs g q fresh hfr CoPset.subseteq_top $$ Hinv Hosfd Hd as %v Hv
  icases Hv with (⟨%b, %hv, Hosfd⟩ | ⟨%hv, Hosfd, Hd⟩ | ⟨%e, %hv, Hosfd⟩)
  · obtain ⟨rfl, hb, hbr⟩ := hv
    wp_auto
    wp_apply wp_slice_literal (V := GoString) [b]
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl1] as %sl' ⟨Hsl, Hcap, -⟩
    iapply IH $$ %false %(b :: rs) %sl' [] [Hosfd] [] [Hsl] Hcap HΦ Hfd
    · ipureintro
      refine ⟨fun h => absurd h Bool.false_ne_true, List.nodup_cons.2 ⟨hbr, hnd⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hb
      · exact hin x hx
    · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hosfd
    · simp only [Bool.false_eq_true, ↓reduceIte]; iempintro
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
      iapply IH $$ %false %rs %sl0 [] [Hosfd] [] Hsl Hcap HΦ Hfd
      · ipureintro; exact ⟨fun h => absurd h Bool.false_ne_true, hnd, hin⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hosfd
      · simp only [Bool.false_eq_true, ↓reduceIte]; iempintro
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

/-- `os.OpenFile(d/b, O_RDONLY, perm)` of the file `b` of a directory `d` of the namespace (of key
`k`), with a fraction of `k`'s `OsMeta`: the file exists (`mo ≠ none`); a read-only fd on `k`, or
an error. -/
theorem os.OpenFile.wp_nsRO (d b k : GoString) (hb : NameOk b) (perm : w32) (dq : DFrac)
    (g : DirG) (hf : g.now !! b = some (.file k)) (dqm : DFrac) (mo : Option OsMeta) :
    {{ osInv (GF := GF) ∗ osDir (GF := GF) d dq g ∗ osMeta (GF := GF) k dqm mo }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #(W64 0))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); ⌜mo ≠ none⌝ ∗ osDir d dq g ∗
        osMeta k dqm mo ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd (child d b) (DFrac.own 1) ∗
            osFd fd (DFrac.own 1) ⟨k, true, false⟩) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝) }} := by
  wp_start as ⟨#Hinv, Hd, Hm⟩
  iloeb as IH generalizing Hd Hm HΦ
  wp_apply wp_osRegimeNs (child d b) d dq g (.inr ⟨b, hb, rfl⟩) CoPset.subseteq_top $$ Hinv Hd as Hd
  rw [os.file_ty_eq, os.File_ty_eq]
  rw [show (W64 0 ||| W64 524288) = flRO from by decide]
  wp_apply wp_osNsOpenFile d b k dq g hb hf dqm mo CoPset.subseteq_top $$ Hinv Hd Hm
    as %fd %e %hmo %hres Hd Hm Hfd
  by_cases he0 : e = W64 0
  · subst he0
    rw [decide_eq_true rfl]
    rw [if_pos (show W64 0 = (0 : w64) from rfl)]
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    iapply HΦ
    iframe Hd Hm
    isplitr
    · ipureintro; exact hmo
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
      iapply IH $$ Hd Hm HΦ
    · rw [decide_eq_false he4]
      wp_auto
      unfold os.model.pathError
      wp_apply wp_errno
      iapply HΦ
      iframe Hd Hm
      isplitr
      · ipureintro; exact hmo
      iright
      ipureintro; exact ⟨(fun h => by cases h), rfl⟩

end proof

end EtcdGrove
end Perennial
