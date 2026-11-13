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

public import LinuxFs.Spec.os.Rename

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

theorem linkError_ty_eq : os.model.LinkError = os.LinkError.ty := by
  unfold os.LinkError.ty; rfl

variable [syscall.Assumptions] in
/-- `&LinkError{op, old, new, Errno(e)}` as an `error`. -/
theorem wp_linkError (op old new : GoString) (e : w64) (Φ : val → IProp GF) :
    (∀ le : Loc, Φ #(interface.mkOk (go.GoType.PointerType os.LinkError.ty) #le)) ⊢
      WP (App (App (App (App (Val os.model.linkError) (Val #op)) (Val #old)) (Val #new))
        (App (Val syscall.model.errno) (Val #e))) {{ Φ }} := by
  iintro HΦ
  wp_apply wp_errno
  unfold os.model.linkError
  rw [linkError_ty_eq]
  wp_auto
  iapply HΦ

theorem os.Rename.wp_proofFileS : os.Rename.specFileS (GF := GF) (hG := hG) := by
  intro d bs d' bt j j' i N N' R dq dq' h h' q1 r1 q2 r2 qc Q hbs hbt hN hN' hkey hsrc htgt hq1 hq2
  wp_start as ⟨#Hos, #Hsi, Hp, Hp', Hperm, Hn1, Hn2, Hau⟩
  imod osNames_next R j N _ h CoPset.subseteq_top $$ Hsi Hn1 with ⟨Hn1, #Hlb1⟩
  imod osNames_next R j' N' _ h' CoPset.subseteq_top $$ Hsi Hn2 with ⟨Hn2, #Hlb2⟩
  ihave #Hlb := osLogLb_max h.next h'.next $$ [Hlb1 Hlb2]
  · iframe #
  iclear Hlb1 Hlb2
  wp_apply wp_osCallBeginS R qc (max h.next h'.next) CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  wp_apply wp_osLstatDirS_mem R d' bt j' N' dq' (DFrac.own q2) h' t s0 qc hbt hN'
    CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp' Hn2 Hk as %isDir %e %hd Hperm Hp' Hn2
  have hd1 : isDir ≠ 1 := fun h1 => by obtain ⟨⟨J, hJ⟩, -⟩ := hd h1; exact htgt J hJ
  rw [decide_eq_false (show isDir ≠ W64 1 from hd1)]
  wp_auto
  ihave HSt : iprop((osAU iprop(osNames j N (DFrac.own r1) h ∗ osNames j' N' (DFrac.own r2) h')
      (renFileOut j j' i N N' bs bt h h' (DFrac.own r1) (DFrac.own r2)) Q ∗
      osNames j N (DFrac.own q1) h ∗ osNames j' N' (DFrac.own q2) h') ∨
    (∃ xs, Q (some xs) ∗ renFileOut j j' i N N' bs bt h h' (DFrac.own q1) (DFrac.own q2) (some xs)))
    $$ [Hau Hn1 Hn2]
  · ileft; iframe
  iloeb as IH generalizing Hperm Hp Hp' HSt HΦ
  wp_apply +noauto wp_osCallBeginS R qc (max h.next h'.next) CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  icases HSt with (⟨Hau, Hn1, Hn2⟩ | ⟨%xs, HQ, Hout⟩)
  · wp_apply +noauto (wp_au_step "Rename" _
      iprop(osNames j N (DFrac.own r1) h ∗ osNames j' N' (DFrac.own r2) h')
      (renFileOut j j' i N N' bs bt h h' (DFrac.own r1) (DFrac.own r2)) Q) $$ Hau [Hn1 Hn2 Hk Hp Hp' HΦ]
    iintro ⟨Hr1, Hr2⟩
    ihave Hw1 := (osNames_join j N q1 r1 h hq1).1 $$ [Hn1 Hr1]
    · iframe
    ihave Hw2 := (osNames_join j' N' q2 r2 h' hq2).1 $$ [Hn2 Hr2]
    · iframe
    iapply wp_osRenameFileS R d bs d' bt j j' i N N' dq dq' h h' t s0 qc hbs hbt hN hN' hkey hsrc
      htgt (Nat.le_trans (Nat.le_max_left _ _) hs) (Nat.le_trans (Nat.le_max_right _ _) hs)
      osN_sub_au osShN_sub_au $$ Hos Hsi Hp Hp' Hw1 Hw2 Hk
    iintro %e Hperm Hp Hp' Hres
    icases Hres with (⟨%he, Hw1, Hw2⟩ | ⟨%x, Hlog, Hw1, Hw2⟩)
    · icases (osNames_join j N q1 r1 h hq1).2 $$ Hw1 with ⟨Hn1, Hr1⟩
      icases (osNames_join j' N' q2 r2 h' hq2).2 $$ Hw2 with ⟨Hn2, Hr2⟩
      by_cases he4 : e = W64 4
      · ileft
        isplitl [Hr1 Hr2]
        · iframe
        iintro Hau
        subst he4
        wp_auto
        iapply IH $$ Hperm Hp Hp' [Hau Hn1 Hn2] HΦ
        ileft; iframe
      · iright
        iexists none
        isplitl [Hr1 Hr2]
        · unfold renFileOut logOut claimOut; iframe
        iintro HQ
        wp_auto
        rw [decide_eq_false (show e ≠ W64 4 from he4)]
        wp_auto
        rw [decide_eq_false (show e ≠ W64 0 from he)]
        wp_auto
        wp_apply wp_linkError
        iintro %le
        iapply HΦ
        iframe
        isplitr
        · ipureintro; intro hc; cases hc
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
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        iapply IH $$ Hperm Hp Hp' [HQ Hout] HΦ
        iright; iexists (x, s0); iframe
      rw [decide_eq_false (show e ≠ W64 4 from he4)]
      wp_auto
      by_cases he0 : e = W64 0
      · rw [decide_eq_true he0]
        wp_auto
        iapply HΦ
        iframe
        ipureintro; intro _; rfl
      rw [decide_eq_false (show e ≠ W64 0 from he0)]
      wp_auto
      wp_apply wp_linkError
      iintro %le
      iapply HΦ
      iframe
      ipureintro; intro _; rfl
  · obtain ⟨x, sx⟩ := xs
    isimp only [renFileOut, logOut, claimOut] at Hout
    icases Hout with ⟨⟨%hlo, Hlo⟩, Hn1, Hn2⟩
    unfold osLogged
    icases Hlo with ⟨%hlo2, #Hle, #Hll⟩
    have habs : (h.log x (renFileEnt j bs j' bt i h' sx) (GMap.delete bs h.cur)).cur !! bs = none := by
      simp only [NamesH.log]; exact GMap.lookup_delete _ _
    wp_apply +noauto wp_osRenameAbsentS R d bs d' bt j j' N dq dq' (DFrac.own q1) _ t s0 qc hbs hbt
      hN habs CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hp' Hn1 Hk
      as %e %he Hperm Hp Hp' Hn1
    ihave Hout : renFileOut j j' i N N' bs bt h h' (DFrac.own q1) (DFrac.own q2) (some (x, sx))
      $$ [Hn1 Hn2]
    · dsimp only [renFileOut, logOut, claimOut, osLogged]; iframe; iframe #
      ipureintro; exact ⟨hlo, hlo2⟩
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ Hperm Hp Hp' [HQ Hout] HΦ
      iright; iexists (x, sx); iframe
    rw [decide_eq_false (show e ≠ W64 4 from he4)]
    wp_auto
    rw [decide_eq_false (show e ≠ W64 0 from he)]
    wp_auto
    wp_apply wp_linkError
    iintro %le
    iapply HΦ
    iframe
    ipureintro; intro _; rfl

end proof

end EtcdGrove
end Perennial
