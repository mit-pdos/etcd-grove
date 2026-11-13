/-
The proof of `Spec/os/OpenFileTruncS.lean`: as `Proof/os/OpenFileS.lean`'s, the model's `EINTR` loop
by Löb induction. Before the file was created, an attempt opens the atomic update around the step
(`wp_au_step`; the claim whole, `wp_osOpenCreateS'` with the name absent, so `O_TRUNC` is
irrelevant): an `EINTR` with no effect aborts, any other result commits. After an attempt created
the file and returned `EINTR`, the retry truncates it (`wp_osOpenTruncS`, with the file's
`trFile`).
-/
module

public import LinuxFs.Proof.os.ErrorOk
public import LinuxFs.Proof.os.OpenFile
public import LinuxFs.Spec.os.OpenFileTruncS

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
  ipureintro; exact ⟨hh.1, fun h => hh.2.1 (hP h), hh.2.2⟩

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
  ipureintro; exact ⟨rfl, fun _ => rfl, rfl, rfl, Nat.le_refl _⟩

/-- An unmapped file's cells: nothing. -/
theorem mcellsAny_of_empty (M : GMap Loc Nat) (hM : M = ∅) (lo hi : Nat) :
    ⊢ mcellsAny (GF := GF) M lo hi := by
  subst hM; unfold mcellsAny; exact BigSepM.bigSepM_empty.2

/-- A file truncated to 0 is a `trFile`, of size 0. -/
theorem trFile_of_rsDone (i : Ino) (m : OsMeta) (n : Nat) (P : Prop) (hmp : m.maps = ∅)
    (hcut : m.cut = none) :
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
  refine ⟨rfl, fun _ => rfl, by simp only [rsPost, announce_maps]; exact hmp, ?_, ?_⟩
  · simp [rsPost, hcut]
  · simp [rsPost, OsMeta.announce]

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions]

theorem os.OpenFile.wp_proofCreateTruncSnc : os.OpenFile.specCreateTruncSnc (GF := GF) (hG := hG) := by
  intro d b flag perm R j dq h q r qc Q hfl hcr htr hb hn hq
  generalize hfl' : flag ||| W64 0x80000 = fl at hfl hcr htr ⊢
  have hnd : ∀ J, h.cur !! b ≠ some (.dir J) := by intro J; rw [hn]; simp
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hau⟩
  imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  ihave HSt : iprop((osAUnc (osNames j (.only [b]) (DFrac.own r) h) (crOut j b h (DFrac.own r)) Q ∗
      osNames j (.only [b]) (DFrac.own q) h) ∨
    (∃ xs, Q (some xs) ∗ crOut j b h (DFrac.own q) (some xs) ∗ crTr False (some xs)))
    $$ [Hau Hn]
  · ileft; iframe
  iloeb as IH generalizing Hperm Hp HSt HΦ
  wp_apply wp_osCallBeginS R qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [os.file_ty_eq, os.File_ty_eq, show flag ||| W64 524288 = fl from hfl']
  (try wp_auto)
  icases HSt with (⟨Hau, Hn⟩ | ⟨%xs, HQ, Hout, Hm⟩)
  · wp_apply +noauto (wp_aunc_step "Open" _ (osNames j (.only [b]) (DFrac.own r) h)
      (crOut j b h (DFrac.own r)) Q) $$ Hau [Hn Hk Hp HΦ]
    iintro Hr
    ihave Hw := (osNames_join j _ q r h hq).1 $$ [Hn Hr]
    · iframe
    iapply wp_osOpenCreateS' R d b j dq h t s0 qc fl hfl hcr (.inr hn) hb hnd hs osN_sub_au
      osShN_sub_au $$ Hos Hsi Hp Hw Hk
    iintro %fd %e Hperm Hp Hres
    icases Hres with (⟨%i, %hi, -, -⟩ | ⟨%hn', %x, %i, Hlog, Hw, Hm, Hr⟩ | ⟨%he, Hw⟩)
    · rw [hn] at hi; cases hi
    · -- the file created
      icases (osNames_join j _ q r _ hq).2 $$ Hw with ⟨Hn, Hr'⟩
      unfold osLogged
      icases Hlog with ⟨%hst, #He, #Hl⟩
      iright
      iexists some (x, s0, i)
      isplitl [Hr']
      · dsimp only [crOut, osLogged, crEnt]; iframe; iframe #
        ipureintro; exact ⟨⟨hn', hs⟩, hst⟩
      iintro HQ
      ihave Hout : crOut j b h (DFrac.own q) (some (x, s0, i)) $$ [Hn]
      · dsimp only [crOut, osLogged, crEnt]; iframe; iframe #
        ipureintro; exact ⟨⟨hn', hs⟩, hst⟩
      icases Hr with (%he | ⟨%he, Hfd⟩)
      · obtain ⟨he0, rfl⟩ := he
        wp_auto
        rw [decide_eq_false (show e ≠ W64 0 from he0)]
        wp_auto
        by_cases he4 : e = W64 4
        · rw [decide_eq_true he4]
          wp_auto
          try rw [os.file_ty_eq]
          try rw [os.File_ty_eq]
          iapply IH $$ Hperm Hp [HQ Hout Hm] HΦ
          iright; iexists (x, s0, i); dsimp only [crTr]; iframe
          iapply trFile_new $$ Hm
        rw [decide_eq_false (show e ≠ W64 4 from he4)]
        wp_auto
        wp_apply os.wp_pathError_ok _ _ e he0 as %pe #Hok
        iapply HΦ
        dsimp only [crTr]
        iframe
        isplitl [Hm]
        · iapply trFile_new $$ Hm
        iright
        isplitr
        · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
        iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok
      · obtain ⟨rfl, hfd0⟩ := he
        wp_auto
        iStructNamed inner
        iapply wp_fupd
        wp_auto
        ipersist name
        ipersist f
        imodintro
        iapply HΦ
        dsimp only [crTr]
        iframe
        isplitl [Hm]
        · iapply trFile_new $$ Hm
        ileft
        iexists fd, i
        iframe
        isplitr
        · ipureintro; exact ⟨rfl, hfd0, rfl⟩
        unfold os.ownFile os.ownOff
        isplitr [off]
        · iexists inner_ptr
          iframe
          isplitl [] <;> iassumption
        · iexists inner_ptr
          iframe
          iassumption
    · -- an error, no effect
      icases (osNames_join j _ q r h hq).2 $$ Hw with ⟨Hn, Hr'⟩
      by_cases he4 : e = W64 4
      · ileft
        iframe Hr'
        iintro Hau
        obtain ⟨-, rfl⟩ := he
        subst he4
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        iapply IH $$ Hperm Hp [Hau Hn] HΦ
        ileft; iframe
      · iright
        iexists none
        isplitl [Hr']
        · dsimp only [crOut]; iexact Hr'
        iintro HQ
        obtain ⟨he0, rfl⟩ := he
        wp_auto
        rw [decide_eq_false (show e ≠ W64 0 from he0)]
        wp_auto
        rw [decide_eq_false (show e ≠ W64 4 from he4)]
        wp_auto
        wp_apply os.wp_pathError_ok _ _ e he0 as %pe #Hok
        iapply HΦ
        iframe
        dsimp only [crOut, crTr]
        iframe
        isplitl []
        · iempintro
        iright
        isplitr
        · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
        iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok
  · obtain ⟨x, sx, i⟩ := xs
    have hi : (h.log x (crEnt j b i sx) (<[b := .file i]> h.cur)).cur !! b = some (.file i) := by
      simp only [NamesH.log]; exact GMap.lookup_insert _ _ _
    isimp only [crOut] at Hout
    icases Hout with ⟨%hc, Hlo, Hn⟩
    isimp only [crTr, trFile] at Hm
    icases Hm with ⟨%m, %bs, Hm, Hb, -, %hmb⟩
    ihave Hc := mcellsAny_of_empty (GF := GF) m.maps hmb.2.2.1 0 (pageEnd m.size)
    wp_apply +noauto wp_osOpenTruncS R d b j i (.only [b]) dq (DFrac.own q) _ t s0 qc fl m bs
      hfl htr hb (by simp [NameSet.Mem]) hi hmb.1 CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hp Hn Hk Hm Hb Hc
      as %fd %e %hres Hperm Hp Hn Htr Hfd
    ihave Hout : crOut j b h (DFrac.own q) (some (x, sx, i)) $$ [Hlo Hn]
    · dsimp only [crOut]; iframe; ipureintro; exact hc
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
      try dsimp only [crTr]
      iframe
      isplitl [Hd]
      · iapply trFile_of_rsDone i m n _ hmb.2.2.1 hmb.2.2.2.1 $$ Hd
      ileft
      iexists fd, i
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, hfd0, rfl⟩
      unfold os.ownFile os.ownOff
      isplitr [off]
      · iexists inner_ptr
        iframe
        isplitl [] <;> iassumption
      · iexists inner_ptr
        iframe
        iassumption
    · iclear Hfd
      have hfd : fd = -1 := by rcases hres with ⟨h, -⟩ | ⟨-, h⟩; exact absurd h he0; exact h
      subst hfd
      ihave Hm : trFile i False $$ [Htr]
      · icases Htr with (⟨-, Hm, Hb, -⟩ | ⟨%n, Hd⟩)
        · ihave Hc := mcellsAny_of_empty (GF := GF) m.maps hmb.2.2.1 0 m.size
          unfold trFile; iexists m, bs; iframe; isplitl [Hc]; · iexact Hc
          ipureintro; exact ⟨hmb.1, False.elim, hmb.2.2⟩
        · iapply trFile_of_rsDone i m n False hmb.2.2.1 hmb.2.2.2.1 $$ Hd
      wp_auto
      rw [decide_eq_false (show e ≠ W64 0 from he0)]
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        iapply IH $$ Hperm Hp [HQ Hout Hm] HΦ
        iright; iexists (x, sx, i); dsimp only [crTr]; iframe
      rw [decide_eq_false (show e ≠ W64 4 from he4)]
      wp_auto
      wp_apply os.wp_pathError_ok _ _ e he0 as %pe #Hok
      iapply HΦ
      dsimp only [crTr]
      iframe
      isplitl [Hm]
      · iapply trFile_mono i False _ (fun h => by cases h) $$ Hm
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
      iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok

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
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm qc ∗
        trFile i False }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #flag)) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osNames j N dqn h ∗
        osCallPerm qc ∗ trFile i (err = interface.nil) ∗
        ((∃ fd : w64, ⌜err = interface.nil ∧ 0 ≤ fd.toInt⌝ ∗ os.ownFile f fd (child d b) (DFrac.own 1) ∗
            os.ownOff f (W64 0) ∗
            osFd fd (DFrac.own 1) (openFd i (flag ||| W64 0x80000))) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝ ∗ fmtErrorOkOrNil err) }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm, Hf⟩
  generalize hfl' : flag ||| W64 0x80000 = fl at hfl htr ⊢
  imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  iloeb as IH generalizing Hperm Hp Hn Hf HΦ
  wp_apply wp_osCallBeginS R qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [os.file_ty_eq, os.File_ty_eq, show flag ||| W64 524288 = fl from hfl']
  (try wp_auto)
  isimp only [trFile] at Hf
  icases Hf with ⟨%m, %bs, Hm, Hb, -, %hmb⟩
  ihave Hc := mcellsAny_of_empty (GF := GF) m.maps hmb.2.2.1 0 (pageEnd m.size)
  wp_apply +noauto wp_osOpenTruncS R d b j i N dq dqn h t s0 qc fl m bs
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
    · iapply trFile_of_rsDone i m n _ hmb.2.2.1 hmb.2.2.2.1 $$ Hd
    ileft
    iexists fd
    iframe
    isplitr
    · ipureintro; exact ⟨rfl, hfd0⟩
    unfold os.ownFile os.ownOff
    isplitr [off]
    · iexists inner_ptr
      iframe
      isplitl [] <;> iassumption
    · iexists inner_ptr
      iframe
      iassumption
  · iclear Hfd
    have hfd : fd = -1 := by rcases hres with ⟨h, -⟩ | ⟨-, h⟩; exact absurd h he0; exact h
    subst hfd
    ihave Hm : trFile i False $$ [Htr]
    · icases Htr with (⟨-, Hm, Hb, -⟩ | ⟨%n, Hd⟩)
      · ihave Hc := mcellsAny_of_empty (GF := GF) m.maps hmb.2.2.1 0 m.size
        unfold trFile; iexists m, bs; iframe; isplitl [Hc]; · iexact Hc
        ipureintro; exact ⟨hmb.1, False.elim, hmb.2.2⟩
      · iapply trFile_of_rsDone i m n False hmb.2.2.1 hmb.2.2.2.1 $$ Hd
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
    wp_apply os.wp_pathError_ok _ _ e he0 as %pe #Hok
    iapply HΦ
    iframe
    isplitl [Hm]
    · iapply trFile_mono i False _ (fun h => by cases h) $$ Hm
    iright
    isplitr
    · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
    iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok

/-- `specCreateTruncS` from `specCreateTruncSnc`: an `osAU` is an `osAUnc`. -/
theorem os.OpenFile.wp_proofCreateTruncS : os.OpenFile.specCreateTruncS (GF := GF) (hG := hG) := by
  intro d b flag perm R j dq h q r qc Q hfl hcr htr hb hn hq
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hau⟩ HΦ
  iapply os.OpenFile.wp_proofCreateTruncSnc d b flag perm R j dq h q r qc Q hfl hcr htr hb hn hq $$ [Hp Hperm Hn Hau] HΦ
  iframe Hos Hsi Hp Hperm Hn
  iapply osAU_osAUnc $$ Hau

end proof

end EtcdGrove
end Perennial
