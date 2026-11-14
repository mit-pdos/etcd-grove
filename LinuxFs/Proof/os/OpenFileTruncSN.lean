/-
The proof of `Spec/os/OpenFileTruncSN.lean`: `Proof/os/OpenFileTruncS.lean`'s proof of
`specCreateTruncSnc`, with the claim on any names `N` containing `b` (`wp_osOpenCreateSN` in place of
`wp_osOpenCreateS'`; `wp_osOpenTruncS` takes any such claim).
-/
module

public import LinuxFs.Proof.os.OpenFileTruncS
public import LinuxFs.Spec.os.OpenFileTruncSN
public import GooseLang.Ext.Fs.TreeSharedCreateN

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions]

theorem os.OpenFile.wp_proofCreateTruncSncN : os.OpenFile.specCreateTruncSncN (GF := GF) (hG := hG) := by
  intro d b flag perm R j N dq h q r qc Q hfl hcr htr hb hN hn hq
  generalize hfl' : flag ||| W64 0x80000 = fl at hfl hcr htr ⊢
  have hnd : ∀ J, h.cur !! b ≠ some (.dir J) := by intro J; rw [hn]; simp
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hau⟩
  imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  ihave HSt : iprop((osAUnc (osNames j N (DFrac.own r) h) (crOutN j N b h (DFrac.own r)) Q ∗
      osNames j N (DFrac.own q) h) ∨
    (∃ xs, Q (some xs) ∗ crOutN j N b h (DFrac.own q) (some xs) ∗ crTr False (some xs)))
    $$ [Hau Hn]
  · ileft; iframe
  iloeb as IH generalizing Hperm Hp HSt HΦ
  wp_apply wp_osCallBeginS R qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [os.file_ty_eq, os.File_ty_eq, show flag ||| W64 524288 = fl from hfl']
  (try wp_auto)
  icases HSt with (⟨Hau, Hn⟩ | ⟨%xs, HQ, Hout, Hm⟩)
  · wp_apply +noauto (wp_aunc_step "Open" _ (osNames j N (DFrac.own r) h)
      (crOutN j N b h (DFrac.own r)) Q) $$ Hau [Hn Hk Hp HΦ]
    iintro Hr
    ihave Hw := (osNames_join j _ q r h hq).1 $$ [Hn Hr]
    · iframe
    iapply wp_osOpenCreateSN R d b j N dq h t s0 qc fl hfl hcr (.inr hn) hb hN hnd hs osN_sub_au
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
      · dsimp only [crOutN, osLogged, crEnt]; iframe; iframe #
        ipureintro; exact ⟨⟨hn', hs⟩, hst⟩
      iintro HQ
      ihave Hout : crOutN j N b h (DFrac.own q) (some (x, s0, i)) $$ [Hn]
      · dsimp only [crOutN, osLogged, crEnt]; iframe; iframe #
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
        · dsimp only [crOutN]; iexact Hr'
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
        dsimp only [crOutN, crTr]
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
    isimp only [crOutN] at Hout
    icases Hout with ⟨%hc, Hlo, Hn⟩
    isimp only [crTr, trFile] at Hm
    icases Hm with ⟨%m, %bs, Hm, Hb, -, %hmb⟩
    ihave Hc := mcellsAny_of_empty (GF := GF) m.maps hmb.2.2.1 0 (pageEnd m.size)
    wp_apply +noauto wp_osOpenTruncS R d b j i N dq (DFrac.own q) _ t s0 qc fl m bs
      hfl htr hb hN hi hmb.1 CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hp Hn Hk Hm Hb Hc
      as %fd %e %hres Hperm Hp Hn Htr Hfd
    ihave Hout : crOutN j N b h (DFrac.own q) (some (x, sx, i)) $$ [Hlo Hn]
    · dsimp only [crOutN]; iframe; ipureintro; exact hc
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

end proof

end EtcdGrove
end Perennial
