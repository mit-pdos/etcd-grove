/-
The proofs of `Spec/os/Rename.lean`: the model's `LstatDir` (a fraction of the target's claim:
not a directory), then its `EINTR` loop by Löb induction, each attempt a `CallBegin` (the log's
length at least both claims' last change, `osNames_next`) and the extension's `Rename`. Before the
rename took effect, an attempt opens the atomic update around the step (`wp_au_step`): the claims
whole, the shared-mode spec of the rename; an `EINTR` with no effect aborts, any other result
commits. After it took effect (an `EINTR` with the effect), the source is gone in the caller's
fraction, and the attempt fails with no effect (`wp_osRenameAbsentS`).
-/
module

public import Spec.os.RenameS
public import GooseLang.Ext.Fs.NoErrSpecsRename
public import GooseLang.Ext.Fs.NoErrSpecsRenameDir
public import Proof.os.ErrorOk
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

set_option hygiene false in
/-- `wp_linkError`: the model's inline `&LinkError{"rename", old, new, modelErrno(e)}` (as an `error`):
`modelErrno`, then the allocation of a fresh `*LinkError` at `le` (its points-to `Hle` dropped). -/
macro "wp_linkError" : tactic => `(tactic| (
  wp_apply os.wp_modelErrno
  (try wp_auto)
  wp_alloc le as Hle
  iclear Hle
  (try wp_auto)))

set_option hygiene false in
/-- `wp_linkError_ok he`: `wp_linkError` for a nonzero errno (`he : e ≠ 0`), the fresh `*LinkError`
at `le` one `fmt` formats (`#Hle : fmtErrorOk`, `os.linkError_fmtErrorOk`), given `#Hsys : syscall.errnoOk`
in context (unhygienic). Needs a `wp_fupd`
goal's update: run it where the goal is a `WP` (it applies `wp_fupd` itself). -/
macro "wp_linkError_ok" he:term : tactic => `(tactic| (
  iapply wp_fupd
  wp_apply os.wp_modelErrno
  (try wp_auto)
  wp_alloc le as Hle
  iStructNamed Hle
  ipersist Op
  ipersist Old
  ipersist New
  ipersist Err
  ihave #Hle := os.linkError_fmtErrorOk le _ _ _ _ $$ Op Old New Err []
  · iapply (errnoErr_fmtErrorOk _ $he) $$ Hsys
  iclear Op Old New Err
  (try wp_auto)
  imodintro))

theorem os.Rename.wp_proofFileSnc : os.Rename.specFileSnc (GF := GF) (hG := hG) := by
  intro d bs d' bt j j' i N N' R dq dq' h h' q1 r1 q2 r2 qc Q hbs hbt hN hN' hkey hsrc htgt hq1 hq2 hsr
  wp_start as ⟨#Hos, #Hsi, Hp, Hp', Hperm, Hn1, Hn2, Hau⟩
  imod osNames_next R j N _ h CoPset.subseteq_top $$ Hsi Hn1 with ⟨Hn1, #Hlb1⟩
  imod osNames_next R j' N' _ h' CoPset.subseteq_top $$ Hsi Hn2 with ⟨Hn2, #Hlb2⟩
  ihave #Hlb := osLogLb_max h.next h'.next $$ [Hlb1 Hlb2]
  · iframe #
  iclear Hlb1 Hlb2
  imod osSharedInv_rootsOk R CoPset.subseteq_top $$ Hsi with %hRo
  icases osPathS_callKey R d _ _ $$ Hp with ⟨Hp, %hkd⟩
  icases osPathS_callKey R d' _ _ $$ Hp' with ⟨Hp', %hkd'⟩
  have hk : callKey R (child d' bt) = callKey R d := by
    rw [callKey_of_sameRoot hRo hsr, hkd]
  ihave Hperm := osCallPerm_congr qc hk.symm $$ Hperm
  try wp_auto
  wp_stub os.fsLstatDir.impl
  wp_apply wp_osCallBeginS R _ qc (max h.next h'.next) CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  -- PORT: which stub? (LstatDirS)
  wp_apply wp_osLstatDirS_mem R d' bt j' N' dq' (DFrac.own q2) h' t s0 qc hbt hN'
    CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp' Hn2 Hk as %isDir %e %hd Hperm Hp' Hn2
  ihave Hperm := osCallPerm_congr qc ((hkd' bt).symm.trans hk) $$ Hperm
  have hd1 : isDir ≠ 1 := fun h1 => by obtain ⟨⟨J, hJ⟩, -⟩ := hd h1; exact htgt J hJ
  (try rw [decide_eq_false (show isDir ≠ W64 1 from hd1)])
  try wp_auto
  ihave HSt : iprop((osAUnc iprop(osNames j N (DFrac.own r1) h ∗ osNames j' N' (DFrac.own r2) h')
      (renFileOut j j' i N N' bs bt h h' (DFrac.own r1) (DFrac.own r2)) Q ∗
      osNames j N (DFrac.own q1) h ∗ osNames j' N' (DFrac.own q2) h') ∨
    (∃ xs, ⌜¬ (FsNoErrOn (· = child d' bt) ∧ PathFits (child d bs) ∧ PathFits (child d' bt))⌝ ∗ Q (some xs) ∗
      renFileOut j j' i N N' bs bt h h' (DFrac.own q1) (DFrac.own q2) (some xs)))
    $$ [Hau Hn1 Hn2]
  · ileft; iframe
  wp_for_bind
  iloeb as IH generalizing Hperm Hp Hp' HSt HΦ
  wp_for_step
  icases osCallPerm_child R d bs _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  wp_stub os.fsRename.impl
  wp_apply +noauto wp_osCallBeginS R _ qc (max h.next h'.next) CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  icases HSt with (⟨Hau, Hn1, Hn2⟩ | ⟨%xs, %hnW, HQ, Hout⟩)
  · wp_apply +noauto (wp_aunc_step "Rename" _
      iprop(osNames j N (DFrac.own r1) h ∗ osNames j' N' (DFrac.own r2) h')
      (renFileOut j j' i N N' bs bt h h' (DFrac.own r1) (DFrac.own r2)) Q) $$ Hau [-]
    iintro ⟨Hr1, Hr2⟩
    ihave Hw1 := (osNames_join j N q1 r1 h hq1).1 $$ [Hn1 Hr1]
    · iframe
    ihave Hw2 := (osNames_join j' N' q2 r2 h' hq2).1 $$ [Hn2 Hr2]
    · iframe
    iapply wp_osRenameFileSW R d bs d' bt j j' i N N' dq dq' h h' t s0 qc hbs hbt hN hN' hkey hsrc
      htgt (Nat.le_trans (Nat.le_max_left _ _) hs) (Nat.le_trans (Nat.le_max_right _ _) hs) hsr
      osN_sub_au osShN_sub_au $$ Hos Hsi Hp Hp' Hw1 Hw2 Hk
    iintro %e Hperm Hp Hp' Hres %hne
    icases Hres with (⟨%he, Hw1, Hw2⟩ | ⟨%x, Hlog, Hw1, Hw2⟩)
    · icases (osNames_join j N q1 r1 h hq1).2 $$ Hw1 with ⟨Hn1, Hr1⟩
      icases (osNames_join j' N' q2 r2 h' hq2).2 $$ Hw2 with ⟨Hn2, Hr2⟩
      by_cases he4 : e = W64 4
      · ileft
        isplitl [Hr1 Hr2]
        · iframe
        iintro Hau
        subst he4
        try wp_auto
        ihave HSt : iprop((osAUnc iprop(osNames j N (DFrac.own r1) h ∗ osNames j' N' (DFrac.own r2) h')
            (renFileOut j j' i N N' bs bt h h' (DFrac.own r1) (DFrac.own r2)) Q ∗
            osNames j N (DFrac.own q1) h ∗ osNames j' N' (DFrac.own q2) h') ∨
          (∃ xs, ⌜¬ (FsNoErrOn (· = child d' bt) ∧ PathFits (child d bs) ∧ PathFits (child d' bt))⌝ ∗ Q (some xs) ∗
            renFileOut j j' i N N' bs bt h h' (DFrac.own q1) (DFrac.own q2) (some xs)))
          $$ [Hau Hn1 Hn2]
        · ileft; iframe
        wp_for_post
        inext
        iapply IH $$ Hperm Hp Hp' HSt HΦ [$] [$] [$]
      · iright
        iexists none
        isplitl [Hr1 Hr2]
        · unfold renFileOut logOut claimOut; iframe
        iintro HQ
        try wp_auto
        (try rw [decide_eq_false (show e ≠ W64 4 from he4)])
        try wp_auto
        (try rw [decide_eq_false (show e ≠ W64 0 from he)])
        try wp_auto
        wp_linkError
        wp_for_post
        iapply HΦ
        iframe
        isplitr
        · ipureintro; exact ⟨fun hc => (by cases hc), fun _ => hne he⟩
        unfold renFileOut logOut claimOut; iframe
    · icases (osNames_join j N q1 r1 _ hq1).2 $$ Hw1 with ⟨Hn1, Hr1⟩
      icases (osNames_join j' N' q2 r2 _ hq2).2 $$ Hw2 with ⟨Hn2, Hr2⟩
      unfold osLogged
      icases Hlog with ⟨%hst, #He, #Hl⟩
      iright
      iexists some (x, s0)
      isplitl [Hr1 Hr2]
      · dsimp only [renFileOut, logOut, claimOut, osLogged, renFileEnt]; iframe; iframe #
        ipureintro; exact ⟨hs, hst⟩
      iintro HQ
      ihave Hout : renFileOut j j' i N N' bs bt h h' (DFrac.own q1) (DFrac.own q2) (some (x, s0))
        $$ [Hn1 Hn2]
      · dsimp only [renFileOut, logOut, claimOut, osLogged, renFileEnt]; iframe; iframe #
        ipureintro; exact ⟨hs, hst⟩
      try wp_auto
      by_cases he4 : e = W64 4
      · (try rw [decide_eq_true he4])
        try wp_auto
        wp_for_post
        inext
        iapply IH $$ Hperm Hp Hp' [HQ Hout] HΦ [$] [$] [$]
        iright; iexists (x, s0); iframe
        ipureintro; exact hne (by rw [he4]; decide)
      (try rw [decide_eq_false (show e ≠ W64 4 from he4)])
      try wp_auto
      by_cases he0 : e = W64 0
      · (try rw [decide_eq_true he0])
        try wp_auto
        wp_for_post
        iapply HΦ
        iframe
        ipureintro; exact ⟨fun _ => rfl, fun hc => absurd rfl hc⟩
      (try rw [decide_eq_false (show e ≠ W64 0 from he0)])
      try wp_auto
      wp_linkError
      wp_for_post
      iapply HΦ
      iframe
      ipureintro; exact ⟨fun _ => rfl, fun _ => hne he0⟩
  · obtain ⟨x, sx⟩ := xs
    isimp only [renFileOut, logOut, claimOut] at Hout
    icases Hout with ⟨⟨%hlo, Hlo⟩, Hn1, Hn2⟩
    unfold osLogged
    icases Hlo with ⟨%hlo2, #Hle, #Hll⟩
    have habs : (h.log x (renFileEnt j bs j' bt i h' sx) (GMap.delete bs h.cur)).cur !! bs = none := by
      simp only [NamesH.log]; exact GMap.lookup_delete _ _
    wp_apply +noauto wp_osRenameAbsentS R d bs d' bt j j' N dq dq' (DFrac.own q1) _ t s0 qc hbs hbt
      hN habs hsr CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hp' Hn1 Hk
      as %e %he Hperm Hp Hp' Hn1
    ihave Hout : renFileOut j j' i N N' bs bt h h' (DFrac.own q1) (DFrac.own q2) (some (x, sx))
      $$ [Hn1 Hn2]
    · dsimp only [renFileOut, logOut, claimOut, osLogged]; iframe; iframe #
      ipureintro; exact ⟨hlo, hlo2⟩
    try wp_auto
    by_cases he4 : e = W64 4
    · (try rw [decide_eq_true he4])
      try wp_auto
      wp_for_post
      inext
      iapply IH $$ Hperm Hp Hp' [HQ Hout] HΦ [$] [$] [$]
      iright; iexists (x, sx); iframe
      ipureintro; exact hnW
    (try rw [decide_eq_false (show e ≠ W64 4 from he4)])
    try wp_auto
    (try rw [decide_eq_false (show e ≠ W64 0 from he)])
    try wp_auto
    wp_linkError
    wp_for_post
    iapply HΦ
    iframe
    ipureintro; exact ⟨fun _ => rfl, fun _ => hnW⟩

/-- `specFileS` from `specFileSnc`: an `osAU` is an `osAUnc`. -/
theorem os.Rename.wp_proofFileS : os.Rename.specFileS (GF := GF) (hG := hG) := by
  intro d bs d' bt j j' i N N' R dq dq' h h' q1 r1 q2 r2 qc Q hbs hbt hN hN' hkey hsrc htgt hq1 hq2 hsr
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hp', Hperm, Hn1, Hn2, Hau⟩ HΦ
  iapply os.Rename.wp_proofFileSnc d bs d' bt j j' i N N' R dq dq' h h' q1 r1 q2 r2 qc Q hbs hbt
    hN hN' hkey hsrc htgt hq1 hq2 hsr $$ [Hp Hp' Hperm Hn1 Hn2 Hau] HΦ
  iframe Hos Hsi Hp Hp' Hperm Hn1 Hn2
  iapply osAU_osAUnc $$ Hau

theorem os.Rename.wp_proofDirSnc : os.Rename.specDirSnc (GF := GF) (hG := hG) := by
  intro d bs bt j J N R qd h q r lb Q hbs hbt hN hN' hne hsrc htgt hq
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, #Hlb0, Hn, Hau⟩
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
  have hd1 : isDir ≠ 1 := fun h1 => by
    obtain ⟨⟨J', hJ⟩, -⟩ := hd h1; rw [htgt] at hJ; cases hJ
  (try rw [decide_eq_false (show isDir ≠ W64 1 from hd1)])
  try wp_auto
  ihave HSt : iprop((osAUnc (osNames j N (DFrac.own r) h) (renDirOut j J N bs bt h (DFrac.own r) lb) Q ∗
      osNames j N (DFrac.own q) h) ∨
    (∃ xs, ⌜¬ (FsNoErrOn (· = child d bt) ∧ PathFits (child d bs) ∧ PathFits (child d bt))⌝ ∗ Q (some xs) ∗ renDirOut j J N bs bt h (DFrac.own q) lb (some xs)))
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
  icases HSt with (⟨Hau, Hn⟩ | ⟨%xs, %hnW, HQ, Hout⟩)
  · wp_apply +noauto (wp_aunc_step "Rename" _ (osNames j N (DFrac.own r) h)
      (renDirOut j J N bs bt h (DFrac.own r) lb) Q) $$ Hau [-]
    iintro Hr
    ihave Hw := (osNames_join j N q r h hq).1 $$ [Hn Hr]
    · iframe
    iapply wp_osRenameDirSW R d bs bt j J N (DFrac.own qd) h t s0 hbs hbt hN hN' hne hsrc htgt
      osN_sub_au osShN_sub_au $$ Hos Hsi Hp Hw Hk
    iintro %e Hperm Hp Hres %hnw
    unfold osNamesAfter
    icases Hres with (⟨%he, Hw⟩ | ⟨%x, Hlog, Hw⟩)
    · icases (osNames_join j N q r h hq).2 $$ Hw with ⟨Hn, Hr⟩
      by_cases he4 : e = W64 4
      · ileft
        iframe Hr
        iintro Hau
        subst he4
        try wp_auto
        ihave HSt : iprop((osAUnc (osNames j N (DFrac.own r) h) (renDirOut j J N bs bt h (DFrac.own r) lb) Q ∗
            osNames j N (DFrac.own q) h) ∨
          (∃ xs, ⌜¬ (FsNoErrOn (· = child d bt) ∧ PathFits (child d bs) ∧ PathFits (child d bt))⌝ ∗ Q (some xs) ∗ renDirOut j J N bs bt h (DFrac.own q) lb (some xs)))
          $$ [Hau Hn]
        · ileft; iframe
        wp_for_post
        inext
        iapply IH $$ Hperm Hp HSt HΦ [$] [$] [$]
      · iright
        iexists none
        isplitl [Hr]
        · unfold renDirOut logOut claimOut; iframe
        iintro HQ
        try wp_auto
        (try rw [decide_eq_false (show e ≠ W64 4 from he4)])
        try wp_auto
        (try rw [decide_eq_false (show e ≠ W64 0 from he)])
        try wp_auto
        wp_linkError
        wp_for_post
        iapply HΦ
        iframe
        isplitr
        · ipureintro; exact ⟨fun hc => (by cases hc), Or.inr ⟨le, rfl⟩, fun _ => hnw he⟩
        unfold renDirOut logOut claimOut; iframe
    · icases (osNames_join j N q r _ hq).2 $$ Hw with ⟨Hn, Hr⟩
      unfold osLogged
      icases Hlog with ⟨%hst, #He, #Hl⟩
      iright
      iexists some (x, s0)
      isplitl [Hr]
      · dsimp only [renDirOut, logOut, claimOut, osLogged, renDirEnt]; iframe; iframe #
        ipureintro; exact ⟨(Nat.max_le.1 hs).2, hst⟩
      iintro HQ
      ihave Hout : renDirOut j J N bs bt h (DFrac.own q) lb (some (x, s0)) $$ [Hn]
      · dsimp only [renDirOut, logOut, claimOut, osLogged, renDirEnt]; iframe; iframe #
        ipureintro; exact ⟨(Nat.max_le.1 hs).2, hst⟩
      try wp_auto
      by_cases he4 : e = W64 4
      · (try rw [decide_eq_true he4])
        try wp_auto
        wp_for_post
        inext
        iapply IH $$ Hperm Hp [HQ Hout] HΦ [$] [$] [$]
        iright; iexists (x, s0); iframe
        ipureintro; exact hnw (by rw [he4]; decide)
      (try rw [decide_eq_false (show e ≠ W64 4 from he4)])
      try wp_auto
      by_cases he0 : e = W64 0
      · (try rw [decide_eq_true he0])
        try wp_auto
        wp_for_post
        iapply HΦ
        iframe
        ipureintro; exact ⟨fun _ => rfl, Or.inl rfl, fun hc => absurd rfl hc⟩
      (try rw [decide_eq_false (show e ≠ W64 0 from he0)])
      try wp_auto
      wp_linkError
      wp_for_post
      iapply HΦ
      iframe
      ipureintro; exact ⟨fun _ => rfl, Or.inr ⟨le, rfl⟩, fun _ => hnw he0⟩
  · obtain ⟨x, sx⟩ := xs
    isimp only [renDirOut, logOut, claimOut] at Hout
    icases Hout with ⟨⟨%hlo, Hlo⟩, Hn⟩
    unfold osLogged
    icases Hlo with ⟨%hlo2, #Hle, #Hll⟩
    have habs : (h.log x (renDirEnt j bs bt J sx)
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
    ihave Hout : renDirOut j J N bs bt h (DFrac.own q) lb (some (x, sx)) $$ [Hn]
    · dsimp only [renDirOut, logOut, claimOut, osLogged]; iframe; iframe #
      ipureintro; exact ⟨hlo, hlo2⟩
    try wp_auto
    by_cases he4 : e = W64 4
    · (try rw [decide_eq_true he4])
      try wp_auto
      wp_for_post
      inext
      iapply IH $$ Hperm Hp [HQ Hout] HΦ [$] [$] [$]
      iright; iexists (x, sx); iframe
      ipureintro; exact hnW
    (try rw [decide_eq_false (show e ≠ W64 4 from he4)])
    try wp_auto
    (try rw [decide_eq_false (show e ≠ W64 0 from he)])
    try wp_auto
    wp_linkError
    wp_for_post
    iapply HΦ
    iframe
    ipureintro; exact ⟨fun _ => rfl, Or.inr ⟨le, rfl⟩, fun _ => hnW⟩

/-- `specDirS` from `specDirSnc`: an `osAU` is an `osAUnc`. -/
theorem os.Rename.wp_proofDirS : os.Rename.specDirS (GF := GF) (hG := hG) := by
  intro d bs bt j J N R qd h q r lb Q hbs hbt hN hN' hne hsrc htgt hq
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hperm, #Hlb, Hn, Hau⟩ HΦ
  iapply os.Rename.wp_proofDirSnc d bs bt j J N R qd h q r lb Q hbs hbt hN hN' hne hsrc htgt hq $$ [Hp Hperm Hn Hau] HΦ
  iframe Hos Hsi Hp Hperm Hn Hlb
  iapply osAU_osAUnc $$ Hau

end proof

end EtcdGrove
end Perennial
