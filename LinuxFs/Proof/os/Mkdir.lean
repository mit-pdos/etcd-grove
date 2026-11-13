/-
The proof of `Spec/os/Mkdir.lean`: the model's `EINTR` loop by Löb induction, each attempt a
`CallBegin` with the whole call permission. Before the `mkdir` took effect, an attempt opens the
atomic update around the step (`wp_au_step`; the claim whole, `wp_osMkdirS`): an `EINTR` with no
effect aborts, any other result commits. After it took effect, the name holds the new directory in
the caller's fraction and a retry fails (`wp_osMkdirS_some`).
-/
module

public import LinuxFs.Spec.os.Mkdir
public import LinuxFs.Proof.os.ErrorOk
public import LinuxFs.Proof.os.SharedExt

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

theorem os.Mkdir.wp_proofS : os.Mkdir.specS (GF := GF) (hG := hG) := by
  intro d b perm R j dq h q r Q hb hn hq
  have hbN : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hau⟩
  imod osLogLb_0 with #Hlb
  ihave HSt : iprop((osAU (osNames j (.only [b]) (DFrac.own r) h) (mkOut j b h (DFrac.own r)) Q ∗
      osNames j (.only [b]) (DFrac.own q) h) ∨
    (∃ xs, Q (some xs) ∗ mkOut j b h (DFrac.own q) (some xs) ∗ mkNew (some xs)))
    $$ [Hau Hn]
  · ileft; iframe
  iloeb as IH generalizing Hperm Hp HSt HΦ
  wp_apply +noauto wp_osCallBeginS R 1 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  icases HSt with (⟨Hau, Hn⟩ | ⟨%xs, HQ, Hout, Hnew⟩)
  · wp_apply +noauto (wp_au_step "Mkdir" _ (osNames j (.only [b]) (DFrac.own r) h)
      (mkOut j b h (DFrac.own r)) Q) $$ Hau [Hn Hk Hp HΦ]
    iintro Hr
    ihave Hw := (osNames_join j _ q r h hq).1 $$ [Hn Hr]
    · iframe
    iapply wp_osMkdirS R d b j dq h t s0 hb hn osN_sub_au osShN_sub_au $$ Hos Hsi Hp Hw Hk
    iintro %e Hperm Hp Hres
    icases Hres with (⟨%he, Hw⟩ | ⟨%x, %J, Hlog, Hw, HJ⟩)
    · icases (osNames_join j _ q r h hq).2 $$ Hw with ⟨Hn, Hr⟩
      by_cases he4 : e = W64 4
      · ileft
        iframe Hr
        iintro Hau
        subst he4
        wp_auto
        iapply IH $$ Hperm Hp [Hau Hn] HΦ
        ileft; iframe
      · iright
        iexists none
        isplitl [Hr]
        · dsimp only [mkOut]; iframe
        iintro HQ
        wp_auto
        rw [decide_eq_false (show e ≠ W64 4 from he4)]
        wp_auto
        rw [decide_eq_false (show e ≠ W64 0 from he)]
        wp_auto
        unfold os.model.pathError
        wp_apply wp_errno
        iapply HΦ
        iframe
        dsimp only [mkOut, mkNew]
        iframe
        ipureintro; intro hc; cases hc
    · icases (osNames_join j _ q r _ hq).2 $$ Hw with ⟨Hn, Hr⟩
      unfold osLogged
      icases Hlog with ⟨%hst, #He, #Hl⟩
      iright
      iexists some (x, s0, J)
      isplitl [Hr]
      · dsimp only [mkOut, mkEnt, osLogged]; iframe; iframe #; ipureintro; exact hst
      iintro HQ
      ihave Hout : mkOut j b h (DFrac.own q) (some (x, s0, J)) $$ [Hn]
      · dsimp only [mkOut, mkEnt, osLogged]; iframe; iframe #; ipureintro; exact hst
      ihave Hnew : mkNew (some (x, s0, J)) $$ [HJ]
      · dsimp only [mkNew]; iexact HJ
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        iapply IH $$ Hperm Hp [HQ Hout Hnew] HΦ
        iright; iexists (x, s0, J); iframe
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
      unfold os.model.pathError
      wp_apply wp_errno
      iapply HΦ
      iframe
      ipureintro; intro _; rfl
  · obtain ⟨x, sx, J⟩ := xs
    isimp only [mkOut, osLogged] at Hout
    icases Hout with ⟨⟨%hst, #He, #Hl⟩, Hn⟩
    have hsome : ((h.log x (mkEnt j b J sx) (<[b := .dir J]> h.cur)).cur !! b).isSome := by
      simp only [NamesH.log]; rw [GMap.lookup_insert]; rfl
    wp_apply +noauto wp_osMkdirS_some R d b j (.only [b]) dq (DFrac.own q) _ t s0 1 hb hbN hsome
      CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
    ihave Hout : mkOut j b h (DFrac.own q) (some (x, sx, J)) $$ [Hn]
    · dsimp only [mkOut, osLogged]; iframe; iframe #; ipureintro; exact hst
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ Hperm Hp [HQ Hout Hnew] HΦ
      iright; iexists (x, sx, J); iframe
    rw [decide_eq_false (show e ≠ W64 4 from he4)]
    wp_auto
    rw [decide_eq_false (show e ≠ W64 0 from he)]
    wp_auto
    unfold os.model.pathError
    wp_apply wp_errno
    iapply HΦ
    iframe
    ipureintro; intro _; rfl

end proof

end EtcdGrove
end Perennial
