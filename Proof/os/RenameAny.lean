/-
The proof of `Spec/os/RenameAny.lean`: as `os.Rename.wp_proofDirSnc` (`Rename.lean`), with the target's
`lstat` reporting a directory as an exit that gives the atomic update back unused, and each attempt's
`rename(2)` the shared-mode `Fs.wp_osRenameDirAnyS` (a logged outcome found the target nothing or a
directory). Lean-first (no Rocq counterpart).
-/
module

public import Spec.os.RenameAny
public import Proof.os.RenameS
public import Proof.os.ErrorOk
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

theorem os.Rename.wp_proofDirAnySnc : os.Rename.specDirAnySnc (GF := GF) (hG := hG) := by
  intro d bs bt j J N R qd h q r lb Q hbs hbt hN hN' hne hsrc hq
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, #Hlb0, Hn, Hau⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  imod osNames_next R j N _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb1⟩
  ihave #Hlb : osLogLb (max h.next lb) $$ []
  · rcases Nat.le_total h.next lb with hle | hle
    · rw [Nat.max_eq_right hle]; iexact Hlb0
    · rw [Nat.max_eq_left hle]; iexact Hlb1
  iclear Hlb0 Hlb1
  icases osCallPerm_child R d bt _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  try wp_auto
  wp_stub os.fsLstatDir.impl
  wp_apply wp_osCallBeginS R _ 1 (max h.next lb) CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  -- PORT: which stub? (LstatDirS)
  wp_apply wp_osLstatDirS_mem R d bt j N (DFrac.own qd) (DFrac.own q) h t s0 1 hbt hN'
    CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %isDir %e %hd Hperm Hp Hn
  by_cases hd1 : isDir = 1
  · -- a directory at the target: Go's `EEXIST`, no `rename(2)`
    (try rw [decide_eq_true (show isDir = W64 1 from hd1)])
    try wp_auto
    wp_linkError_ok (hd hd1).2
    iapply HΦ
    iframe Hp Hperm
    isplitl []
    · iapply fmtErrorOkOrNil_of $$ Hle
    ileft
    iframe Hn Hau
    ipureintro; exact ⟨fun hc => (by cases hc), Or.inr ⟨le, rfl⟩⟩
  (try rw [decide_eq_false (show isDir ≠ W64 1 from hd1)])
  try wp_auto
  ihave HSt : iprop((osAUnc (osNames j N (DFrac.own r) h) (renDirOutA j J N bs bt h (DFrac.own r) lb) Q ∗
      osNames j N (DFrac.own q) h) ∨
    (∃ xs, Q (some xs) ∗ renDirOutA j J N bs bt h (DFrac.own q) lb (some xs)))
    $$ [Hau Hn]
  · ileft; iframe
  wp_for_bind
  iloeb as IH generalizing Hperm Hp HSt HΦ
  wp_for_step
  icases osCallPerm_child R d bs _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  wp_stub os.fsRename.impl
  wp_apply +noauto wp_osCallBeginS R _ 1 (max h.next lb) CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  icases HSt with (⟨Hau, Hn⟩ | ⟨%xs, HQ, Hout⟩)
  · wp_apply +noauto (wp_aunc_step "Rename" _ (osNames j N (DFrac.own r) h)
      (renDirOutA j J N bs bt h (DFrac.own r) lb) Q) $$ Hau [-]
    iintro Hr
    ihave Hw := (osNames_join j N q r h hq).1 $$ [Hn Hr]
    · iframe
    iapply wp_osRenameDirAnyS R d bs bt j J N (DFrac.own qd) h t s0 hbs hbt hN hN' hne hsrc
      osN_sub_au osShN_sub_au $$ Hos Hsi Hp Hw Hk
    iintro %e Hperm Hp Hres
    icases Hres with (⟨%he, Hw⟩ | ⟨%hR, %x, Hlog, Hw⟩)
    · icases (osNames_join j N q r h hq).2 $$ Hw with ⟨Hn, Hr⟩
      by_cases he4 : e = W64 4
      · ileft
        iframe Hr
        iintro Hau
        subst he4
        try wp_auto
        ihave HSt : iprop((osAUnc (osNames j N (DFrac.own r) h) (renDirOutA j J N bs bt h (DFrac.own r) lb) Q ∗
            osNames j N (DFrac.own q) h) ∨
          (∃ xs, Q (some xs) ∗ renDirOutA j J N bs bt h (DFrac.own q) lb (some xs)))
          $$ [Hau Hn]
        · ileft; iframe
        wp_for_post
        inext
        iapply IH $$ Hperm Hp HSt HΦ [$] [$] [$]
      · iright
        iexists none
        isplitl [Hr]
        · unfold renDirOutA logOut claimOut; iframe
          ipureintro; intro hc; cases hc
        iintro HQ
        try wp_auto
        (try rw [decide_eq_false (show e ≠ W64 4 from he4)])
        try wp_auto
        (try rw [decide_eq_false (show e ≠ W64 0 from he)])
        try wp_auto
        wp_linkError_ok he
        wp_for_post
        iapply HΦ
        iframe Hp Hperm
        isplitl []
        · iapply fmtErrorOkOrNil_of $$ Hle
        iright
        iexists none
        iframe HQ
        isplitr
        · ipureintro; exact ⟨fun hc => (by cases hc), Or.inr ⟨le, rfl⟩⟩
        unfold renDirOutA logOut claimOut; iframe
        ipureintro; intro hc; cases hc
    · icases (osNames_join j N q r _ hq).2 $$ Hw with ⟨Hn, Hr⟩
      unfold osLogged
      icases Hlog with ⟨%hst, #He, #Hl⟩
      iright
      iexists some (x, s0)
      isplitl [Hr]
      · dsimp only [renDirOutA, logOut, claimOut, osLogged, renDirEntA]; iframe; iframe #
        ipureintro; exact ⟨fun _ => hR, (Nat.max_le.1 hs).2, hst⟩
      iintro HQ
      ihave Hout : renDirOutA j J N bs bt h (DFrac.own q) lb (some (x, s0)) $$ [Hn]
      · dsimp only [renDirOutA, logOut, claimOut, osLogged, renDirEntA]; iframe; iframe #
        ipureintro; exact ⟨fun _ => hR, (Nat.max_le.1 hs).2, hst⟩
      try wp_auto
      by_cases he4 : e = W64 4
      · (try rw [decide_eq_true he4])
        try wp_auto
        wp_for_post
        inext
        iapply IH $$ Hperm Hp [HQ Hout] HΦ [$] [$] [$]
        iright; iexists (x, s0); iframe
      (try rw [decide_eq_false (show e ≠ W64 4 from he4)])
      try wp_auto
      by_cases he0 : e = W64 0
      · (try rw [decide_eq_true he0])
        try wp_auto
        wp_for_post
        iapply HΦ
        iframe Hp Hperm
        isplitl []
        · iapply fmtErrorOkOrNil_nil
        iright
        iexists some (x, s0)
        iframe HQ Hout
        ipureintro; exact ⟨fun _ => rfl, Or.inl rfl⟩
      (try rw [decide_eq_false (show e ≠ W64 0 from he0)])
      try wp_auto
      wp_linkError_ok he0
      wp_for_post
      iapply HΦ
      iframe Hp Hperm
      isplitl []
      · iapply fmtErrorOkOrNil_of $$ Hle
      iright
      iexists some (x, s0)
      iframe HQ Hout
      ipureintro; exact ⟨fun _ => rfl, Or.inr ⟨le, rfl⟩⟩
  · obtain ⟨x, sx⟩ := xs
    isimp only [renDirOutA, logOut, claimOut] at Hout
    icases Hout with ⟨%hRt, ⟨%hlo, Hlo⟩, Hn⟩
    unfold osLogged
    icases Hlo with ⟨%hlo2, #Hle, #Hll⟩
    have habs : (h.log x (renDirEntA j bs bt J (h.cur !! bt) sx)
        (restrictN N (<[bt := .dir J]> (GMap.delete bs h.cur)))).cur !! bs = none := by
      simp only [NamesH.log]
      rw [restrictN_lookup N _ bs hN, GMap.lookup_insert_ne _ _ (Ne.symm hne)]
      exact GMap.lookup_delete _ _
    ihave Hpp := (osPathS_frac R d qd.half qd.half j).1 $$ [Hp]
    · rw [Qp.half_add_half]; iexact Hp
    icases Hpp with ⟨Hp1, Hp2⟩
    icases osPathS_sameRoot R d bs bt _ j $$ Hp1 with ⟨Hp1, %hsr⟩
    wp_apply +noauto wp_osRenameAbsentS R d bs d bt j j N (DFrac.own qd.half) (DFrac.own qd.half)
      (DFrac.own q) _ t s0 1 hbs hbt hN habs hsr CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hp1 Hp2 Hn Hk as %e %he Hperm Hp1 Hp2 Hn
    ihave Hp := (osPathS_frac R d qd.half qd.half j).2 $$ [Hp1 Hp2]
    · iframe
    rw [Qp.half_add_half]
    ihave Hout : renDirOutA j J N bs bt h (DFrac.own q) lb (some (x, sx)) $$ [Hn]
    · dsimp only [renDirOutA, logOut, claimOut, osLogged]; iframe; iframe #
      ipureintro; exact ⟨hRt, hlo, hlo2⟩
    try wp_auto
    by_cases he4 : e = W64 4
    · (try rw [decide_eq_true he4])
      try wp_auto
      wp_for_post
      inext
      iapply IH $$ Hperm Hp [HQ Hout] HΦ [$] [$] [$]
      iright; iexists (x, sx); iframe
    (try rw [decide_eq_false (show e ≠ W64 4 from he4)])
    try wp_auto
    (try rw [decide_eq_false (show e ≠ W64 0 from he)])
    try wp_auto
    wp_linkError_ok he
    wp_for_post
    iapply HΦ
    iframe Hp Hperm
    isplitl []
    · iapply fmtErrorOkOrNil_of $$ Hle
    iright
    iexists some (x, sx)
    iframe HQ Hout
    ipureintro; exact ⟨fun _ => rfl, Or.inr ⟨le, rfl⟩⟩

end proof

end EtcdGrove
end Perennial

end
