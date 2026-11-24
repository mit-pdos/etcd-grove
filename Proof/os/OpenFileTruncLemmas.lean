/-
The lemmas of `os.OpenFile`'s truncating opens (`trFile_mono`, ..., `trFile_of_rsDone`) and the
retry's spec `os.OpenFile.wp_truncS` (a name holding a file: truncated again), moved unchanged out of
the proof file `OpenFileTruncS.lean` (import tiers, 2026-11-19: the WAL's `PipeLemmas` and
`durable`'s `WriteOpen` use them, and a proof file is imported by linking modules only).
-/
module

public import Proof.os.ErrorOk
public import Proof.syscall.ErrorOk
public import Spec.os.OpenFileTruncS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

theorem trFile_mono (i : Ino) (P P' : Prop) (hP : P' → P) :
    trFile (GF := GF) i P ⊢ trFile i P' := by
  unfold trFile
  iintro ⟨%m, %xs, Hm, Hb, Hc, %hh⟩
  iexists m, xs
  iframe
  ipureintro
  exact ⟨hh.1, fun h => hh.2.1 (hP h), hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1, hh.2.2.2.2.2.1,
    fun h => hh.2.2.2.2.2.2 (hP h)⟩

theorem osBytes_nil (i : Ino) (off : Nat) (dq : DFrac) : ⊢ osBytes (GF := GF) i off dq [] := by
  unfold osBytes bytesG
  iapply BigSepL.bigSepL_nil.2
  iempintro

/-- A new file is a `trFile`, of size 0. -/
theorem trFile_new (i : Ino) (P : Prop) :
    osMeta (GF := GF) i (DFrac.own 1) newMeta ⊢ trFile i P := by
  iintro Hm
  unfold trFile
  iexists newMeta, []
  iframe
  rw [show newMeta.size = 0 from rfl]
  isplitl []
  · iapply osBytes_nil
  isplitl []
  · iapply (mcellsAny_empty (GF := GF) newMeta.maps 0)
  have hz : newMeta.zf = some 0 := by simp [initMeta, newFile, OsFile.ofBytes, OsFile.ofDisk, pageEnd]
  have hc : newMeta.cz = 0 := rfl
  ipureintro
  exact ⟨rfl, fun _ => rfl, rfl, rfl, Nat.le_refl _, ⟨0, hz, Nat.le_refl _⟩,
    fun _ => ⟨0, hz, Nat.le_refl _, by rw [hc]; simp [pageEnd]⟩⟩

/-- An unmapped file's cells: nothing. -/
theorem mcellsAny_of_empty (M : GMap Loc Nat) (hM : M = ∅) (lo hi : Nat) :
    ⊢ mcellsAny (GF := GF) M lo hi := by
  subst hM; unfold mcellsAny; exact BigSepM.bigSepM_empty.2

/-- A file truncated to 0 is a `trFile`, of size 0. -/
theorem trFile_of_rsDone (i : Ino) (m : OsMeta) (n : Nat) (P : Prop) (hmp : m.maps = ∅)
    (hcut : m.cut = none) (hzf : m.ZfGe) :
    rsDone (GF := GF) true i 0 0 m n ⊢ trFile i P := by
  unfold rsDone trFile
  iintro ⟨%zs, %hz, Hm, -, -⟩
  iexists rsPost true m 0 0, []
  iframe
  have h0 : (rsPost true m 0 0).size = 0 := rfl
  rw [h0]
  isplitl []
  · iapply osBytes_nil
  isplitl []
  · iapply (mcellsAny_empty (GF := GF) (rsPost true m 0 0).maps 0)
  ipureintro
  refine ⟨rfl, fun _ => rfl, by simp only [rsPost, announce_maps]; exact hmp, ?_, ?_,
    OsMeta.zfGe_rsPost hzf true 0 0 (Nat.zero_le _), fun _ => OsMeta.zeroPg_rsPost_true hzf 0⟩
  · simp [rsPost, hcut]
  · simp [rsPost, OsMeta.announce]

end lemmas

section truncS
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions]

/-- `os.OpenFile(d/b, flag, perm)`, `flag` with `O_TRUNC` (with or without `O_CREATE`), of a name
holding the file `i` (a leftover `N.tmp`), with a fraction of a claim on names containing `b` and
the file whole (`trFile i False`: any size): nothing logged; on success a fresh fd on `i` and the
file of size 0; on failure the file truncated or not (`trFile i False`). Each `EINTR` retry
truncates again. A plain triple: no claim changes. -/
theorem os.OpenFile.wp_truncS (d b : GoString) (flag : w64) (perm : w32) (R : Roots) (j i : Ino)
    (N : NameSet) (dq dqn : DFrac) (h : NamesH) (qc : Qp)
    (hfl : OpenFlagsOk (flag ||| W64 0x80000).toNat)
    (htr : (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 1) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc ∗
        trFile i False }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #flag)) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osNames j N dqn h ∗
        osCallPerm (callKey R d) qc ∗ trFile i (err = interface.nil) ∗
        ((∃ fd : w64, ⌜err = interface.nil ∧ 0 ≤ fd.toInt⌝ ∗ os.ownFile f fd (child d b) (DFrac.own 1) ∗
            os.ownOff f (W64 0) ∗
            osFd fd (DFrac.own 1) (openFd i (flag ||| W64 0x80000))) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝ ∗ fmtErrorOkOrNil err ∗
           ⌜¬ (FsNoErrOn (· = child d b) ∧ PathFits (child d b))⌝) }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm, Hf⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  generalize hfl' : flag ||| W64 0x80000 = fl at hfl htr ⊢
  imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  iloeb as IH generalizing Hperm Hp Hn Hf HΦ
  icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  wp_apply wp_osCallBeginS R _ qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [os.file_ty_eq, os.File_ty_eq, show flag ||| W64 524288 = fl from hfl']
  (try wp_auto)
  isimp only [trFile] at Hf
  icases Hf with ⟨%m, %bs, Hm, Hb, -, %hmb⟩
  ihave Hc := mcellsAny_of_empty (GF := GF) m.maps hmb.2.2.1 0 (pageEnd m.size)
  wp_apply +noauto wp_osOpenTruncSW R d b j i N dq dqn h t s0 qc fl m bs
    hfl htr hb hN hi hmb.1 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hp Hn Hk Hm Hb Hc
    as %fd %e %hres Hperm Hp Hn Htr Hfd
  by_cases he0 : e = W64 0
  · subst he0
    have hfd0 : 0 ≤ fd.toInt := by rcases hres with ⟨-, h⟩ | ⟨h, -⟩; exact h; exact absurd rfl h
    ihave Hfd := (show (if W64 0 = (0 : w64) then osFd (GF := GF) fd (DFrac.own 1)
        (openFd i fl) else emp) ⊢ osFd fd (DFrac.own 1) (openFd i fl)
      by split
         · iintro H; iexact H
         · exact absurd rfl ‹_›) $$ Hfd
    icases Htr with (⟨%he, -⟩ | ⟨%n, Hd⟩)
    · exact absurd rfl he
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    iapply HΦ
    iframe
    isplitl [Hd]
    · iapply trFile_of_rsDone i m n _ hmb.2.2.1 hmb.2.2.2.1 hmb.2.2.2.2.2.1 $$ Hd
    ileft
    iexists fd
    iframe
    isplitr
    · ipureintro; exact ⟨rfl, hfd0⟩
    unfold os.ownFile os.ownOff
    isplitr [off]
    · iexists inner_ptr
      iframe
      (repeat' isplitl []) <;> iassumption
    · iexists inner_ptr
      iframe
      iassumption
  · iclear Hfd
    have hfd : fd = -1 := by rcases hres with ⟨h, -⟩ | ⟨-, h, -⟩; exact absurd h he0; exact h
    have hW := fun hne : e ≠ 0 => (hres.resolve_left (fun h => hne h.1)).2.2
    subst hfd
    ihave Hm : trFile i False $$ [Htr]
    · icases Htr with (⟨-, Hm, Hb, -⟩ | ⟨%n, Hd⟩)
      · ihave Hc := mcellsAny_of_empty (GF := GF) m.maps hmb.2.2.1 0 m.size
        unfold trFile; iexists m, bs; iframe; isplitl [Hc]; · iexact Hc
        ipureintro; exact ⟨hmb.1, False.elim, hmb.2.2⟩
      · iapply trFile_of_rsDone i m n False hmb.2.2.1 hmb.2.2.2.1 hmb.2.2.2.2.2.1 $$ Hd
    wp_auto
    rw [decide_eq_false (show e ≠ W64 0 from he0)]
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      iapply IH $$ Hperm Hp Hn Hm HΦ
    rw [decide_eq_false (show e ≠ W64 4 from he4)]
    wp_auto
    wp_apply os.wp_pathError_ok _ _ e he0 $$ Hsys as %pe #Hok
    iapply HΦ
    iframe
    isplitl [Hm]
    · iapply trFile_mono i False _ (fun h => by cases h) $$ Hm
    iright
    isplitr
    · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
    isplitl []
    · iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok
    ipureintro; exact (hW he0).resolve_left (fun h4 => he4 (by rw [h4]; rfl))

end truncS

end EtcdGrove
end Perennial
