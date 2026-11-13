/-
`os.RemoveAll`'s model on the directory it removes (`TrustedCode/os.lean`), in the tree's shared
mode, for `Proof/os/RemoveAll.lean`: the `unlink` loop on a name holding no file, and the `rmdir`
loop on the directory `d/b` (`J`) under the guard, over the state `rmAllOut` (the claims on `b` and
on `J`'s names; `b` as it was or its `rmdir` logged). Lean-first; untrusted.
-/
module

public import LinuxFs.Proof.os.RemoveAllLeaf

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
variable [os.Assumptions] [os.fileStat.FieldAssumptions]

/-- `unlink` loop on a name holding no file (a fraction of the claim on it): an errno, no
effect. -/
theorem os.model.wp_unlinkLoop_nofile (p c : GoString) (R : Roots) (J : Ino) (dq dqn : DFrac)
    (hc : NamesH) (qc : Qp) (hcN : NameOk c) (hnf : ∀ i, hc.cur !! c ≠ some (.file i)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗
        osNames J (.only [c]) dqn hc ∗ osCallPerm qc }}
      (App (Val os.model.unlinkLoop) (Val #(child p c)))
    {{ (e : w64), RET #e; ⌜e ≠ 0⌝ ∗ osPathS R p dq J ∗ osNames J (.only [c]) dqn hc ∗
        osCallPerm qc }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm Hp Hn
  wp_apply +noauto wp_osCallBeginS R qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  wp_auto
  wp_apply +noauto wp_osUnlinkS_none R p c J dq dqn hc t s0 qc hcN hnf CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
  wp_auto
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    iapply IH $$ Hperm Hp Hn HΦ
  rw [decide_eq_false he4]
  wp_auto
  iapply HΦ
  iframe
  ipureintro; exact he

/-- The name `b` after the `rmdir` of `J` was logged holds nothing. -/
theorem os.rmDir_cur_none (j : Ino) (b : GoString) (J : Ino) (h : NamesH) (x s : Nat) :
    (h.log x (rmDirEnt j b J s) (restrictN (.only [b]) (GMap.delete b h.cur))).cur !! b = none := by
  simp only [NamesH.log]
  rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem])]; exact GMap.lookup_delete _ _

/-- `rmdir` loop on the directory `d/b` (`J`, the state `rmAllOut`), under the guard `t`: an
errno; the state, perhaps with the `rmdir` logged (only on an empty `J`). -/
theorem os.model.wp_rmdirLoop_dirSt (d b : GoString) (j J : Ino) (R : Roots) (qd : Qp)
    (h hJ0 : NamesH) (q g : Qp) (t sg : Nat) (hb : NameOk b) (hJ : h.cur !! b = some (.dir J))
    (hqg : q + g = 1) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ rmAllOut j b J h hJ0 ∗
        osCallPerm q ∗ osGuardS t sg g ∗ osLogLb sg }}
      (App (Val os.model.rmdirLoop) (Val #(child d b)))
    {{ (e : w64), RET #e; osPathS R d (DFrac.own qd) j ∗ rmAllOut j b J h hJ0 ∗ osCallPerm q ∗
        osGuardS t sg g }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hst, Hperm, Hg, #Hlsg⟩
  iloeb as IH generalizing Hperm Hp Hst Hg
  wp_apply +noauto wp_osCallBeginS R q sg CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlsg as %t1 %s0 %hs Hk Hls
  iclear Hls
  wp_auto
  isimp only [rmAllOut] at Hst
  icases Hst with ⟨%h', %hJ', Hb, HJ, %hsub, Hor⟩
  icases Hor with (%hh | ⟨%x, %s, Hlog, %hlog⟩)
  · subst hh
    by_cases hne : ∃ c, (hJ'.cur !! c).isSome
    · obtain ⟨c, hc⟩ := hne
      rw [← Qp.half_add_half qd]
      icases (osPathS_frac R d qd.half qd.half j).1 $$ Hp with ⟨Hp1, Hp2⟩
      icases os.osPathS_borrow R d b j J qd.half h' hb hJ $$ [Hp1 Hb] with ⟨%ε, Hpc, Hback⟩
      · iframe
      wp_apply +noauto wp_osRmdirS_nonempty R d b j J (.except []) (DFrac.own qd.half) (DFrac.own ε)
        (DFrac.own 1) hJ' c t1 s0 q hb (by simp [NameSet.Mem]) hc CoPset.subseteq_top
        CoPset.subseteq_top $$ Hos Hsi Hp2 Hpc HJ Hk as %e %he Hperm Hp2 Hpc HJ
      icases Hback $$ Hpc with ⟨Hp1, Hb⟩
      ihave Hp := (osPathS_frac R d qd.half qd.half j).2 $$ [Hp1 Hp2]
      · iframe
      rw [Qp.half_add_half qd]
      ihave Hst : rmAllOut j b J h' hJ0 $$ [Hb HJ]
      · unfold rmAllOut; iexists h', hJ'; iframe; isplitr
        · ipureintro; exact hsub
        ileft; ipureintro; rfl
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        iapply IH $$ Hperm Hp Hst Hg HΦ
      rw [decide_eq_false he4]
      wp_auto
      iapply HΦ
      iframe
    · have hemp : hJ'.cur = ∅ := by
        apply (GMap.lookup_empty_iff _).1
        intro c
        cases hcc : hJ'.cur !! c with
        | none => rfl
        | some _ => exact absurd ⟨c, by simp [hcc]⟩ hne
      wp_apply +noauto wp_osRmdirSG R d b j J (DFrac.own qd) h' hJ' t1 s0 t sg q g hqg hs hb hJ hemp
        CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hb HJ Hk Hg
        as %e Hperm Hg Hp HJ Hres
      unfold osNamesAfter
      ihave Hst : rmAllOut j b J h' hJ0 $$ [Hres HJ]
      · unfold rmAllOut
        icases Hres with (⟨-, Hb⟩ | ⟨%x, Hlog, Hb⟩)
        · iexists h', hJ'; iframe; isplitr
          · ipureintro; exact hsub
          ileft; ipureintro; rfl
        · iexists _, hJ'; iframe; isplitr
          · ipureintro; exact hsub
          iright; iexists x, s0
          isplitl
          · dsimp only [rmDirEnt]; iexact Hlog
          ipureintro; exact ⟨rfl, hemp⟩
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        iapply IH $$ Hperm Hp Hst Hg HΦ
      rw [decide_eq_false he4]
      wp_auto
      iapply HΦ
      iframe
  · obtain ⟨rfl, hemp⟩ := hlog
    wp_apply +noauto wp_osRmdirS_none R d b j (DFrac.own qd) (DFrac.own 1) _ t1 s0 q hb
      (fun J' h'' => by rw [os.rmDir_cur_none] at h''; cases h'') CoPset.subseteq_top
      CoPset.subseteq_top $$ Hos Hsi Hp Hb Hk as %e %he Hperm Hp Hb
    ihave Hst : rmAllOut j b J h hJ0 $$ [Hb HJ Hlog]
    · unfold rmAllOut; iexists _, hJ'; iframe; isplitr
      · ipureintro; exact hsub
      iright; iexists x, s
      isplitl
      · iexact Hlog
      ipureintro; exact ⟨rfl, hemp⟩
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ Hperm Hp Hst Hg HΦ
    rw [decide_eq_false he4]
    wp_auto
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
