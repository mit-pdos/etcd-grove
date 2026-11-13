/-
The proof of `Spec/os/OpenFileS.lean`: the model's `EINTR` loop by Löb induction, each attempt a
`CallBegin` (the log's length at least the claim's last change, `osNames_next`) and the
extension's `Open`. Before the file was created, an attempt opens the atomic update around the
step (`wp_au_step`; the claim whole, `wp_osOpenCreateS`): an `EINTR` with no effect aborts, any
other result commits. After an attempt created it and returned `EINTR`, the caller's fraction of
the claim names the new file, and the retry opens it (`wp_osOpenFileS`).
-/
module

public import LinuxFs.Proof.os.ErrorOk
public import LinuxFs.Proof.os.OpenFile
public import LinuxFs.Spec.os.OpenFileS

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

theorem os.OpenFile.wp_proofCreateS : os.OpenFile.specCreateS (GF := GF) (hG := hG) := by
  intro d b flag perm R j dq h q r qc Q hfl hcr htr hb hnd hq
  generalize hfl' : flag ||| W64 0x80000 = fl at hfl hcr htr ⊢
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hau⟩
  imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  ihave HSt : iprop((osAU (osNames j (.only [b]) (DFrac.own r) h) (crOut j b h (DFrac.own r)) Q ∗
      osNames j (.only [b]) (DFrac.own q) h) ∨
    (∃ xs, Q (some xs) ∗ crOut j b h (DFrac.own q) (some xs) ∗ crMeta (some xs)))
    $$ [Hau Hn]
  · ileft; iframe
  iloeb as IH generalizing Hperm Hp HSt HΦ
  wp_apply wp_osCallBeginS R qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [os.file_ty_eq, os.File_ty_eq, show flag ||| W64 524288 = fl from hfl']
  (try wp_auto)
  icases HSt with (⟨Hau, Hn⟩ | ⟨%xs, HQ, Hout, Hm⟩)
  · wp_apply +noauto (wp_au_step "Open" _ (osNames j (.only [b]) (DFrac.own r) h)
      (crOut j b h (DFrac.own r)) Q) $$ Hau [Hn Hk Hp HΦ]
    iintro Hr
    ihave Hw := (osNames_join j _ q r h hq).1 $$ [Hn Hr]
    · iframe
    iapply wp_osOpenCreateS R d b j dq h t s0 qc fl hfl hcr htr hb hnd hs osN_sub_au osShN_sub_au
      $$ Hos Hsi Hp Hw Hk
    iintro %fd %e Hperm Hp Hres
    icases Hres with (⟨%i, %hi, Hw, Hr⟩ | ⟨%hn, %x, %i, Hlog, Hw, Hm, Hr⟩ | ⟨%he, Hw⟩)
    · -- the file existed
      icases (osNames_join j _ q r h hq).2 $$ Hw with ⟨Hn, Hr'⟩
      icases Hr with (%he | ⟨%he, Hfd⟩)
      · by_cases he4 : e = W64 4
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
          dsimp only [crOut, crMeta]
          iframe
          isplitl []
          · iempintro
          iright
          isplitr
          · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
          iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok
      · iright
        iexists none
        isplitl [Hr']
        · dsimp only [crOut]; iexact Hr'
        iintro HQ
        obtain ⟨rfl, hfd0⟩ := he
        wp_auto
        iStructNamed inner
        iapply wp_fupd
        wp_auto
        ipersist name
        ipersist f
        imodintro
        iapply HΦ
        iframe
        dsimp only [crOut, crMeta]
        iframe
        ileft
        iexists fd, i
        iframe
        isplitr
        · ipureintro; exact ⟨rfl, hfd0, hi⟩
        unfold os.ownFile
        iexists inner_ptr
        iframe
        isplitl [] <;> iassumption
    · -- the file created
      icases (osNames_join j _ q r _ hq).2 $$ Hw with ⟨Hn, Hr'⟩
      unfold osLogged
      icases Hlog with ⟨%hst, #He, #Hl⟩
      iright
      iexists some (x, s0, i)
      isplitl [Hr']
      · dsimp only [crOut, osLogged, crEnt]; iframe; iframe #
        ipureintro; exact ⟨⟨hn, hs⟩, hst⟩
      iintro HQ
      ihave Hout : crOut j b h (DFrac.own q) (some (x, s0, i)) $$ [Hn]
      · dsimp only [crOut, osLogged, crEnt]; iframe; iframe #
        ipureintro; exact ⟨⟨hn, hs⟩, hst⟩
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
          iright; iexists (x, s0, i); dsimp only [crMeta]; iframe
        rw [decide_eq_false (show e ≠ W64 4 from he4)]
        wp_auto
        wp_apply os.wp_pathError_ok _ _ e he0 as %pe #Hok
        iapply HΦ
        dsimp only [crMeta]
        iframe
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
        dsimp only [crMeta]
        iframe
        ileft
        iexists fd, i
        iframe
        isplitr
        · ipureintro; exact ⟨rfl, hfd0, rfl⟩
        unfold os.ownFile
        iexists inner_ptr
        iframe
        isplitl [] <;> iassumption
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
        dsimp only [crOut, crMeta]
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
    wp_apply +noauto wp_osOpenFileS R d b j i (.only [b]) dq (DFrac.own q) _ t s0 qc fl
      hfl htr hb
      (by simp [NameSet.Mem]) hi CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk
      as %fd %e %hres Hperm Hp Hn Hfd
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
      iexists fd, i
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, hfd0, rfl⟩
      unfold os.ownFile
      iexists inner_ptr
      iframe
      isplitl [] <;> iassumption
    · iclear Hfd
      have hfd : fd = -1 := by rcases hres with ⟨h, -⟩ | ⟨-, h⟩; exact absurd h he0; exact h
      subst hfd
      wp_auto
      rw [decide_eq_false (show e ≠ W64 0 from he0)]
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        iapply IH $$ Hperm Hp [HQ Hout Hm] HΦ
        iright; iexists (x, sx, i); dsimp only [crMeta]; iframe
      rw [decide_eq_false (show e ≠ W64 4 from he4)]
      wp_auto
      wp_apply os.wp_pathError_ok _ _ e he0 as %pe #Hok
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
      iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok

end proof

end EtcdGrove
end Perennial
