/-
The proof of `Spec/os/OpenFileTruncS.lean`: as `Proof/os/OpenFileS.lean`'s, the model's `EINTR` loop
by Löb induction. Before the file was created, an attempt opens the atomic update around the step
(`wp_au_step`; the claim whole, `wp_osOpenCreateS'` with the name absent, so `O_TRUNC` is
irrelevant): an `EINTR` with no effect aborts, any other result commits. After an attempt created
the file and returned `EINTR`, the retry truncates it (`wp_osOpenTruncS`, with the file's
`trFile`).
-/
module

public import Proof.os.OpenFileTruncLemmas
public import Spec.os.OpenFileS
public import Spec.os.OpenFileTruncS
public import Proof.os.ErrorOk
public import Proof.os.IgnoringEINTR
public import Proof.os.ForLoeb

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
variable [os.Assumptions]

theorem os.OpenFile.wp_proofCreateTruncSnc : os.OpenFile.specCreateTruncSnc (GF := GF) (hG := hG) := by
  intro d b flag perm R j dq h q r qc Q hfl hcr htr hb hn hq
  generalize hfl' : flag ||| W64 0x80000 = fl at hfl hcr htr ⊢
  have hnd : ∀ J, h.cur !! b ≠ some (.dir J) := by intro J; rw [hn]; simp
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hau⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  ihave HSt : iprop((osAUnc (osNames j (.only [b]) (DFrac.own r) h) (crOut j b h (DFrac.own r)) Q ∗
      osNames j (.only [b]) (DFrac.own q) h) ∨
    (∃ xs, Q (some xs) ∗ crOut j b h (DFrac.own q) (some xs) ∗ crTr False (some xs)))
    $$ [Hau Hn]
  · ileft; iframe
  wp_for_bind
  iloeb as IH generalizing Hperm Hp HSt HΦ
  wp_for_step
  icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  try wp_auto
  wp_open_stub
  wp_apply wp_osCallBeginS R _ qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  try rw [os.file_ty_eq]
  try rw [os.File_ty_eq]
  try rw [show flag ||| W64 524288 = fl from hfl']
  (try wp_auto)
  icases HSt with (⟨Hau, Hn⟩ | ⟨%xs, HQ, Hout, Hm⟩)
  · wp_apply +noauto (wp_aunc_step "Open" _ (osNames j (.only [b]) (DFrac.own r) h)
      (crOut j b h (DFrac.own r)) Q) $$ Hau [Hn Hk Hp HΦ «$res0» «$res1» perm flag name]
    iintro Hr
    ihave Hw := (osNames_join j _ q r h hq).1 $$ [Hn Hr]
    · iframe
    iapply wp_osOpenCreateSW R d b j dq h t s0 qc fl hfl hcr (.inr hn) hb hnd hs osN_sub_au
      osShN_sub_au $$ Hos Hsi Hp Hw Hk
    iintro %fd %e %hW Hperm Hp Hres
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
        try wp_auto
        rw [decide_eq_false (show e ≠ W64 0 from he0)]
        try wp_auto
        by_cases he4 : e = W64 4
        · rw [decide_eq_true he4]
          try wp_auto
          try rw [os.file_ty_eq]
          try rw [os.File_ty_eq]
          wp_for_post
          inext
          iapply IH $$ Hperm Hp [HQ Hout Hm] HΦ [$] [$] [$] [$] [$]
          iright; iexists (x, s0, i); dsimp only [crTr]; iframe
          iapply trFile_new $$ Hm
        rw [decide_eq_false (show e ≠ W64 4 from he4)]
        try wp_auto
        wp_apply os.wp_modelErrno
        try wp_auto
        wp_apply os.wp_modelPathError_ok _ _ e he0 $$ Hsys as %pe #Hok
        try wp_auto
        wp_for_post
        iapply HΦ
        dsimp only [crTr]
        iframe
        isplitl [Hm]
        · iapply trFile_new $$ Hm
        iright
        isplitr
        · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
        isplitl []
        · iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok
        ipureintro; exact (hW he0).resolve_left (fun h4 => he4 (by rw [h4]; rfl))
      · obtain ⟨rfl, hfd0⟩ := he
        try wp_auto
        os_newfile
        wp_for_post_core
        iapply wp_fupd
        try wp_auto
        ipersist name
        ipersist f
        ipersist nonblock
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
        · iexists _
          iframe
          (repeat' isplitl []) <;> iassumption
        · iexists _
          isplitl []
          · iexact f
          (try rw [show (W64 0 : w64) = 0 from rfl])
          iexact off
    · -- an error, no effect
      icases (osNames_join j _ q r h hq).2 $$ Hw with ⟨Hn, Hr'⟩
      by_cases he4 : e = W64 4
      · ileft
        iframe Hr'
        iintro Hau
        obtain ⟨-, rfl⟩ := he
        subst he4
        try wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        wp_for_post
        inext
        iapply IH $$ Hperm Hp [Hau Hn] HΦ [$] [$] [$] [$] [$]
        ileft; iframe
      · iright
        iexists none
        isplitl [Hr']
        · dsimp only [crOut]; iexact Hr'
        iintro HQ
        obtain ⟨he0, rfl⟩ := he
        try wp_auto
        rw [decide_eq_false (show e ≠ W64 0 from he0)]
        try wp_auto
        rw [decide_eq_false (show e ≠ W64 4 from he4)]
        try wp_auto
        wp_apply os.wp_modelErrno
        try wp_auto
        wp_apply os.wp_modelPathError_ok _ _ e he0 $$ Hsys as %pe #Hok
        try wp_auto
        wp_for_post
        iapply HΦ
        iframe
        dsimp only [crOut, crTr]
        iframe
        isplitl []
        · iempintro
        iright
        isplitr
        · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
        isplitl []
        · iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok
        ipureintro; exact (hW he0).resolve_left (fun h4 => he4 (by rw [h4]; rfl))
  · obtain ⟨x, sx, i⟩ := xs
    have hi : (h.log x (crEnt j b i sx) (<[b := .file i]> h.cur)).cur !! b = some (.file i) := by
      simp only [NamesH.log]; exact GMap.lookup_insert _ _ _
    isimp only [crOut] at Hout
    icases Hout with ⟨%hc, Hlo, Hn⟩
    isimp only [crTr, trFile] at Hm
    icases Hm with ⟨%m, %bs, Hm, Hb, -, %hmb⟩
    ihave Hc := mcellsAny_of_empty (GF := GF) m.maps hmb.2.2.1 0 (pageEnd m.size)
    wp_apply +noauto wp_osOpenTruncSW R d b j i (.only [b]) dq (DFrac.own q) _ t s0 qc fl m bs
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
      try wp_auto
      os_newfile
      wp_for_post_core
      iapply wp_fupd
      try wp_auto
      ipersist name
      ipersist f
      ipersist nonblock
      imodintro
      iapply HΦ
      try dsimp only [crTr]
      iframe
      isplitl [Hd]
      · iapply trFile_of_rsDone i m n _ hmb.2.2.1 hmb.2.2.2.1 hmb.2.2.2.2.2.1 $$ Hd
      ileft
      iexists fd, i
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, hfd0, rfl⟩
      unfold os.ownFile os.ownOff
      isplitr [off]
      · iexists _
        iframe
        (repeat' isplitl []) <;> iassumption
      · iexists _
        isplitl []
        · iexact f
        (try rw [show (W64 0 : w64) = 0 from rfl])
        iexact off
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
      try wp_auto
      rw [decide_eq_false (show e ≠ W64 0 from he0)]
      try wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        try wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        wp_for_post
        inext
        iapply IH $$ Hperm Hp [HQ Hout Hm] HΦ [$] [$] [$] [$] [$]
        iright; iexists (x, sx, i); dsimp only [crTr]; iframe
      rw [decide_eq_false (show e ≠ W64 4 from he4)]
      try wp_auto
      wp_apply os.wp_modelErrno
      try wp_auto
      wp_apply os.wp_modelPathError_ok _ _ e he0 $$ Hsys as %pe #Hok
      try wp_auto
      wp_for_post
      iapply HΦ
      dsimp only [crTr]
      iframe
      isplitl [Hm]
      · iapply trFile_mono i False _ (fun h => by cases h) $$ Hm
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
      isplitl []
      · iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok
      ipureintro; exact (hW he0).resolve_left (fun h4 => he4 (by rw [h4]; rfl))

/-- `specCreateTruncS` from `specCreateTruncSnc`: an `osAU` is an `osAUnc`. -/
theorem os.OpenFile.wp_proofCreateTruncS : os.OpenFile.specCreateTruncS (GF := GF) (hG := hG) := by
  intro d b flag perm R j dq h q r qc Q hfl hcr htr hb hn hq
  iintro %Φ ⟨#Hpkg, #Hos, #Hsi, Hp, Hperm, Hn, Hau⟩ HΦ
  iapply os.OpenFile.wp_proofCreateTruncSnc d b flag perm R j dq h q r qc Q hfl hcr htr hb hn hq $$ [Hp Hperm Hn Hau] HΦ
  iframe Hpkg Hos Hsi Hp Hperm Hn
  iapply osAU_osAUnc $$ Hau

end proof

end EtcdGrove
end Perennial
