/-
The proof of `Spec/os/RemoveN.lean`: `Proof/os/Remove.lean`'s proof of `specFileSnc` with the claim
on any set of names `N` (`N.Mem b`), over the generalized extension specs of `Proof/os/UnlinkN.lean`.
-/
module

public import Spec.os.RemoveN
public import Proof.os.ErrorOk
public import Proof.os.SharedExt
public import Proof.os.UnlinkN

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
  icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  try wp_auto
  wp_stub os.fsRmdir.impl
  wp_apply wp_osCallBeginS R _ qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t1 %s1 %hs1 Hk1 Hls1
  iclear Hls1
  -- PORT: which stub? (RmdirSN)
  wp_apply wp_osRmdirSN_none R d b j N dq (DFrac.own q) _ t1 s1 qc hb hbN $hnd CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk1 as %e1 %he1 Hperm Hp Hn
  by_cases he14 : e1 = W64 4
  · rw [decide_eq_true he14]
    try wp_auto
    iapply IH2 $$ Hperm Hp Hn HΦ
    all_goals iframe
  rw [decide_eq_false he14]
  try wp_auto
  rw [decide_eq_false (show e1 ≠ W64 0 from he1)]
  try wp_auto
  unfold os.model.pathError
  by_cases h20 : e1 = W64 20
  · rw [decide_eq_true h20]
    try wp_auto
    wp_apply wp_errno
    iapply HΦ
    ($post)
  · rw [decide_eq_false h20]
    try wp_auto
    wp_apply wp_errno
    iapply HΦ
    ($post)))

theorem os.Remove.wp_proofFileSncN : os.Remove.specFileSncN (GF := GF) (hG := hG) := by
  intro d b j i N R dq h q r qc Q hb hbN hi hq
  have habs : ∀ x s, (h.log x (⟨.remove j b (.file i), s⟩ : LogEntry)
      (restrictN N (GMap.delete b h.cur))).cur !! b = none := by
    intro x s; simp only [NamesH.log]
    rw [restrictN_lookup _ _ _ hbN]; exact GMap.lookup_delete _ _
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hau⟩
  imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  ihave HSt : iprop((osAUnc (osNames j N (DFrac.own r) h) (rmFileOutN j N b i h (DFrac.own r)) Q ∗
      osNames j N (DFrac.own q) h) ∨
    (∃ xs, Q (some xs) ∗ rmFileOutN j N b i h (DFrac.own q) (some xs)))
    $$ [Hau Hn]
  · ileft; iframe
  iloeb as IH generalizing Hperm Hp HSt HΦ
  icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  wp_apply +noauto wp_osCallBeginS R _ qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  icases HSt with (⟨Hau, Hn⟩ | ⟨%xs, HQ, Hout⟩)
  · wp_apply +noauto (wp_aunc_step "Unlink" _ (osNames j N (DFrac.own r) h)
      (rmFileOutN j N b i h (DFrac.own r)) Q) $$ Hau [Hn Hk Hp HΦ]
    iintro Hr
    ihave Hw := (osNames_join j _ q r h hq).1 $$ [Hn Hr]
    · iframe
    iapply wp_osUnlinkSN R d b j i N dq h t s0 qc hb hbN hi hs osN_sub_au osShN_sub_au
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
        try wp_auto
        iapply IH $$ Hperm Hp [Hau Hn] HΦ
        ileft; iframe
      · iright
        iexists none
        isplitl [Hr']
        · dsimp only [rmFileOutN, logOut, claimOut]; iframe
        iintro HQ
        try wp_auto
        rw [decide_eq_false (show e ≠ W64 4 from he4)]
        try wp_auto
        rw [decide_eq_false (show e ≠ W64 0 from he)]
        try wp_auto
        rmdir_loop (fun J hJ => by rw [hi] at hJ; cases hJ) =>
          iframe
          dsimp only [rmFileOutN, logOut, claimOut]
          iframe
          ipureintro; intro hc; cases hc
    · -- the unlink logged
      icases (osNames_join j _ q r _ hq).2 $$ Hw with ⟨Hn, Hr'⟩
      unfold osLogged
      icases Hlog with ⟨%hst, #He, #Hl⟩
      iright
      iexists some (x, s0)
      isplitl [Hr']
      · dsimp only [rmFileOutN, logOut, claimOut, osLogged, rmFileEnt]; iframe; iframe #
        ipureintro; exact ⟨hs, hst⟩
      iintro HQ
      try wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        try wp_auto
        iapply IH $$ Hperm Hp [HQ Hn] HΦ
        iright; iexists (x, s0)
        dsimp only [rmFileOutN, logOut, claimOut, osLogged, rmFileEnt]; iframe; iframe #
        ipureintro; exact ⟨hs, hst⟩
      rw [decide_eq_false (show e ≠ W64 4 from he4)]
      try wp_auto
      by_cases he0 : e = W64 0
      · rw [decide_eq_true he0]
        try wp_auto
        iapply HΦ
        iframe
        dsimp only [rmFileOutN, logOut, claimOut, osLogged, rmFileEnt]; iframe; iframe #
        ipureintro; exact ⟨fun _ => rfl, hs, hst⟩
      rw [decide_eq_false (show e ≠ W64 0 from he0)]
      try wp_auto
      rmdir_loop (fun J hJ => by simp [habs] at hJ) =>
        iframe
        dsimp only [rmFileOutN, logOut, claimOut, osLogged, rmFileEnt]; iframe; iframe #
        ipureintro; exact ⟨fun _ => rfl, hs, hst⟩
  · -- committed: the name is gone in the caller's fraction
    obtain ⟨x, sx⟩ := xs
    isimp only [rmFileOutN, logOut, claimOut] at Hout
    icases Hout with ⟨⟨%hlo, Hlo⟩, Hn⟩
    unfold osLogged
    icases Hlo with ⟨%hlo2, #Hle, #Hll⟩
    wp_apply +noauto wp_osUnlinkSN_none R d b j N dq (DFrac.own q)
      (h.log x (rmFileEnt j b i sx) (restrictN N (GMap.delete b h.cur))) t s0 qc hb hbN
      (fun i' hJ => by simp [rmFileEnt, habs] at hJ) CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
    try wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      try wp_auto
      iapply IH $$ Hperm Hp [HQ Hn] HΦ
      iright; iexists (x, sx)
      dsimp only [rmFileOutN, logOut, claimOut, osLogged]; iframe; iframe #
      ipureintro; exact ⟨hlo, hlo2⟩
    rw [decide_eq_false (show e ≠ W64 4 from he4)]
    try wp_auto
    rw [decide_eq_false (show e ≠ W64 0 from he)]
    try wp_auto
    rmdir_loop (fun J hJ => by simp [rmFileEnt, habs] at hJ) =>
      iframe
      dsimp only [rmFileOutN, logOut, claimOut, osLogged]; iframe; iframe #
      ipureintro; exact ⟨fun _ => rfl, hlo, hlo2⟩

end proof

end EtcdGrove
end Perennial
