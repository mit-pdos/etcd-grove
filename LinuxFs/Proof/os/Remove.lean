/-
The proof of `Spec/os/Remove.lean`: the model's `unlink` loop by Löb induction, each attempt a
`CallBegin` (the log's length at least the claim's last change, `osNames_next`). Before the unlink
took effect, an attempt opens the atomic update around the step (`wp_au_step`; the claim whole,
`wp_osUnlinkS`): an `EINTR` with no effect aborts, any other result commits. After it took effect,
the name is gone in the caller's fraction and a retry fails (`wp_osUnlinkS_none`). The `rmdir`
loop after a failed unlink (`rmdir_loop`) fails on a name holding no directory
(`wp_osRmdirS_none`).
-/
module

public import LinuxFs.Spec.os.Remove
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

set_option hygiene false in
/-- `Remove`'s `rmdir(2)` loop, unrolled once, on a name holding no directory (`hnd`), with a
fraction of its claim (`Hn`): each attempt a nonzero errno with no effect, `EINTR` retried; leaves
the goal after the error is built (`Φ` of it, with `Hp`, `Hperm`, `Hn` back). -/
local macro "rmdir_loop" hnd:term " => " post:tacticSeq : tactic => `(tactic| (
  iloeb as IH2 generalizing Hperm Hp Hn
  wp_apply wp_osCallBeginS R qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t1 %s1 %hs1 Hk1 Hls1
  iclear Hls1
  wp_apply wp_osRmdirS_none R d b j dq (DFrac.own q) _ t1 s1 qc hb $hnd CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk1 as %e1 %he1 Hperm Hp Hn
  by_cases he14 : e1 = W64 4
  · rw [decide_eq_true he14]
    wp_auto
    iapply IH2 $$ Hperm Hp Hn HΦ
    all_goals iframe
  rw [decide_eq_false he14]
  wp_auto
  rw [decide_eq_false (show e1 ≠ W64 0 from he1)]
  wp_auto
  unfold os.model.pathError
  by_cases h20 : e1 = W64 20
  · rw [decide_eq_true h20]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    ($post)
  · rw [decide_eq_false h20]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    ($post)))

theorem os.Remove.wp_proofFileS : os.Remove.specFileS (GF := GF) (hG := hG) := by
  intro d b j i R dq h q r qc Q hb hi hq
  have hbN : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
  have habs : ∀ x s, (h.log x (⟨.remove j b (.file i), s⟩ : LogEntry)
      (restrictN (.only [b]) (GMap.delete b h.cur))).cur !! b = none := by
    intro x s; simp only [NamesH.log]
    rw [restrictN_lookup _ _ _ hbN]; exact GMap.lookup_delete _ _
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hau⟩
  imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  ihave HSt : iprop((osAU (osNames j (.only [b]) (DFrac.own r) h) (rmFileOut j b i h (DFrac.own r)) Q ∗
      osNames j (.only [b]) (DFrac.own q) h) ∨
    (∃ xs, Q (some xs) ∗ rmFileOut j b i h (DFrac.own q) (some xs)))
    $$ [Hau Hn]
  · ileft; iframe
  iloeb as IH generalizing Hperm Hp HSt HΦ
  wp_apply +noauto wp_osCallBeginS R qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  icases HSt with (⟨Hau, Hn⟩ | ⟨%xs, HQ, Hout⟩)
  · wp_apply +noauto (wp_au_step "Unlink" _ (osNames j (.only [b]) (DFrac.own r) h)
      (rmFileOut j b i h (DFrac.own r)) Q) $$ Hau [Hn Hk Hp HΦ]
    iintro Hr
    ihave Hw := (osNames_join j _ q r h hq).1 $$ [Hn Hr]
    · iframe
    iapply wp_osUnlinkS R d b j i dq h t s0 qc hb hi hs osN_sub_au osShN_sub_au
      $$ Hos Hsi Hp Hw Hk
    iintro %e Hperm Hp Hres
    unfold osNamesAfter
    icases Hres with (⟨%he, Hw⟩ | ⟨%x, Hlog, Hw⟩)
    · -- no effect
      icases (osNames_join j _ q r h hq).2 $$ Hw with ⟨Hn, Hr'⟩
      by_cases he4 : e = W64 4
      · ileft
        iframe Hr'
        iintro Hau
        subst he4
        wp_auto
        iapply IH $$ Hperm Hp [Hau Hn] HΦ
        ileft; iframe
      · iright
        iexists none
        isplitl [Hr']
        · dsimp only [rmFileOut, logOut, claimOut]; iframe
        iintro HQ
        wp_auto
        rw [decide_eq_false (show e ≠ W64 4 from he4)]
        wp_auto
        rw [decide_eq_false (show e ≠ W64 0 from he)]
        wp_auto
        rmdir_loop (fun J hJ => by rw [hi] at hJ; cases hJ) =>
          iframe
          dsimp only [rmFileOut, logOut, claimOut]
          iframe
          ipureintro; intro hc; cases hc
    · -- the unlink logged
      icases (osNames_join j _ q r _ hq).2 $$ Hw with ⟨Hn, Hr'⟩
      unfold osLogged
      icases Hlog with ⟨%hst, #He, #Hl⟩
      iright
      iexists some (x, s0)
      isplitl [Hr']
      · dsimp only [rmFileOut, logOut, claimOut, osLogged, rmFileEnt]; iframe; iframe #
        ipureintro; exact ⟨hs, hst⟩
      iintro HQ
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        iapply IH $$ Hperm Hp [HQ Hn] HΦ
        iright; iexists (x, s0)
        dsimp only [rmFileOut, logOut, claimOut, osLogged, rmFileEnt]; iframe; iframe #
        ipureintro; exact ⟨hs, hst⟩
      rw [decide_eq_false (show e ≠ W64 4 from he4)]
      wp_auto
      by_cases he0 : e = W64 0
      · rw [decide_eq_true he0]
        wp_auto
        iapply HΦ
        iframe
        dsimp only [rmFileOut, logOut, claimOut, osLogged, rmFileEnt]; iframe; iframe #
        ipureintro; exact ⟨fun _ => rfl, hs, hst⟩
      rw [decide_eq_false (show e ≠ W64 0 from he0)]
      wp_auto
      rmdir_loop (fun J hJ => by simp [habs] at hJ) =>
        iframe
        dsimp only [rmFileOut, logOut, claimOut, osLogged, rmFileEnt]; iframe; iframe #
        ipureintro; exact ⟨fun _ => rfl, hs, hst⟩
  · -- committed: the name is gone in the caller's fraction
    obtain ⟨x, sx⟩ := xs
    isimp only [rmFileOut, logOut, claimOut] at Hout
    icases Hout with ⟨⟨%hlo, Hlo⟩, Hn⟩
    unfold osLogged
    icases Hlo with ⟨%hlo2, #Hle, #Hll⟩
    wp_apply +noauto wp_osUnlinkS_none R d b j dq (DFrac.own q)
      (h.log x (rmFileEnt j b i sx) (restrictN (.only [b]) (GMap.delete b h.cur))) t s0 qc hb
      (fun i' hJ => by simp [rmFileEnt, habs] at hJ) CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ Hperm Hp [HQ Hn] HΦ
      iright; iexists (x, sx)
      dsimp only [rmFileOut, logOut, claimOut, osLogged]; iframe; iframe #
      ipureintro; exact ⟨hlo, hlo2⟩
    rw [decide_eq_false (show e ≠ W64 4 from he4)]
    wp_auto
    rw [decide_eq_false (show e ≠ W64 0 from he)]
    wp_auto
    rmdir_loop (fun J hJ => by simp [rmFileEnt, habs] at hJ) =>
      iframe
      dsimp only [rmFileOut, logOut, claimOut, osLogged]; iframe; iframe #
      ipureintro; exact ⟨fun _ => rfl, hlo, hlo2⟩

end proof

end EtcdGrove
end Perennial
