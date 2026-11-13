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

/-- The whole claim on a directory's names splits off the name `c`. -/
theorem os.osNames_split1 (R : Roots) (J : Ino) (c : GoString) (hJ : NamesH) :
    osSharedInv (GF := GF) R -∗ osNames J (.except []) (DFrac.own 1) hJ ={⊤}=∗
      osNames J (.only [c]) (DFrac.own 1) (hJ.restrict J (.only [c])) ∗
      osNames J (.except [c]) (DFrac.own 1) (hJ.restrict J (.except [c])) := by
  have h := osNames_split (GF := GF) (E := ⊤) R J (.except []) [c] hJ CoPset.subseteq_top
  have h1 : (NameSet.except []).inter [c] = .only [c] := by simp [NameSet.inter]
  have h2 : (NameSet.except []).diff [c] = .except [c] := by simp [NameSet.diff]
  rw [h1, h2] at h
  exact h

/-- The claims on `c` and on the other names of a directory merge into the whole claim; its
entries are theirs. -/
theorem os.osNames_merge1 (R : Roots) (J : Ino) (c : GoString) (hc hr : NamesH) :
    osSharedInv (GF := GF) R -∗ osNames J (.only [c]) (DFrac.own 1) hc -∗
      osNames J (.except [c]) (DFrac.own 1) hr ={⊤}=∗
      ∃ h'', osNames J (.except []) (DFrac.own 1) h'' ∗
        ⌜h''.cur !! c = hc.cur !! c ∧ ∀ x, x ≠ c → h''.cur !! x = hr.cur !! x⌝ := by
  iintro #Hsi Hc Hr
  imod osNames_merge (GF := GF) (E := ⊤) R J (.only [c]) (.except [c]) (.except []) hc hr
    (fun x => by by_cases hx : x = c <;> simp [NameSet.Mem, hx]) CoPset.subseteq_top
    $$ Hsi Hc Hr with ⟨%h'', Hn, %hres⟩
  obtain ⟨e1, e2, -⟩ := hres
  have hc1 := congrArg (fun h => h.cur !! c) e1
  have hc2 := fun x => congrArg (fun h => h.cur !! x) e2
  simp only [NamesH.restrict] at hc1 hc2
  imodintro
  iexists h''
  iframe
  ipureintro
  refine ⟨?_, fun x hx => ?_⟩
  · have hm : (NameSet.only [c]).Mem c := by simp [NameSet.Mem]
    rw [restrictN_lookup _ _ _ hm, restrictN_lookup _ _ _ hm] at hc1
    exact hc1
  · have hm : (NameSet.except [c]).Mem x := by simp [NameSet.Mem, hx]
    have := hc2 x
    rw [restrictN_lookup _ _ _ hm, restrictN_lookup _ _ _ hm] at this
    exact this

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

/-- `open` loop (read-only) of the directory `j` (a spine to it): an error, or a shared directory
fd on it. -/
theorem os.model.wp_openLoop_spine (p : GoString) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq j ∗ osCallPerm qc }}
      (App (Val os.model.openLoop) (Val #p))
    {{ (fd e : w64), RET (PairV #fd #e); osPathS R p dq j ∗ osCallPerm qc ∗
        (⌜e ≠ 0⌝ ∨ ⌜e = 0⌝ ∗ osDirFdS fd j .idle) }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm⟩
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm Hp
  wp_apply +noauto wp_osCallBeginS R qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  wp_auto
  wp_apply +noauto wp_osOpenDirS R p j dq t s0 qc CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hp Hk as %fd %e %hres Hperm Hp Hfd
  wp_auto
  by_cases he0 : e = W64 0
  · subst he0
    ihave Hfd := Hfd $$ %rfl
    rw [decide_eq_false (show W64 0 ≠ W64 4 by decide)]
    wp_auto
    iapply HΦ
    iframe
    iright
    iframe
    ipureintro; rfl
  · iclear Hfd
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ Hperm Hp HΦ
    rw [decide_eq_false he4]
    wp_auto
    iapply HΦ
    iframe
    ileft; ipureintro; exact he0

/-- `model.closeFd` of a shared directory fd. -/
theorem os.model.wp_closeFd_dir (fd : w64) (j : Ino) (ph : DirPhS) :
    {{ osInv (GF := GF) ∗ osDirFdS fd j ph }}
      (App (Val os.model.closeFd) (Val #fd))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, Hfd⟩
  wp_apply wp_osFdKindDirS fd j ph CoPset.subseteq_top $$ Hos Hfd as Hfd
  wp_apply wp_osDirCloseS fd j ph CoPset.subseteq_top $$ Hos Hfd as %e
  iapply HΦ; itrivial

/-- `rmAllOut` with `b` still the directory `J`. -/
def os.rmPresent (j : Ino) (b : GoString) (J : Ino) (h hJ0 : NamesH) : IProp GF :=
  iprop(∃ hJ', osNames j (.only [b]) (DFrac.own 1) h ∗ osNames J (.except []) (DFrac.own 1) hJ' ∗
    ⌜EntsSub hJ'.cur hJ0.cur⌝)

theorem os.rmPresent_out (j : Ino) (b : GoString) (J : Ino) (h hJ0 : NamesH) :
    os.rmPresent (GF := GF) j b J h hJ0 ⊢ rmAllOut j b J h hJ0 := by
  unfold os.rmPresent rmAllOut
  iintro ⟨%hJ', Hb, HJ, %hsub⟩
  iexists h, hJ'
  iframe
  isplitr
  · ipureintro; exact hsub
  ileft; ipureintro; rfl

/-- `unlink` loop on the directory `d/b` (the state `rmAllOut`): an errno, no effect. -/
theorem os.model.wp_unlinkLoop_dirSt (d b : GoString) (j J : Ino) (R : Roots) (dq : DFrac)
    (h hJ0 : NamesH) (qc : Qp) (hb : NameOk b) (hJ : h.cur !! b = some (.dir J)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ rmAllOut j b J h hJ0 ∗
        osCallPerm qc }}
      (App (Val os.model.unlinkLoop) (Val #(child d b)))
    {{ (e : w64), RET #e; ⌜e ≠ 0⌝ ∗ osPathS R d dq j ∗ rmAllOut j b J h hJ0 ∗ osCallPerm qc }} := by
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hst, Hperm⟩ HΦ
  isimp only [rmAllOut] at Hst
  icases Hst with ⟨%h', %hJ', Hb, HJ, %hsub, Hor⟩
  icases Hor with (%hh | ⟨%x, %s, Hlog, %hlog⟩)
  · subst hh
    wp_apply os.model.wp_unlinkLoop_nofile d b R j dq (DFrac.own 1) h' qc hb
      (fun i hi => by rw [hJ] at hi; cases hi) $$ [Hp Hb Hperm] as %e ⟨%he, Hp, Hb, Hperm⟩
    · iframe; iframe #
    iapply HΦ
    iframe
    isplitr
    · ipureintro; exact he
    unfold rmAllOut
    iexists h', hJ'; iframe; isplitr
    · ipureintro; exact hsub
    ileft; ipureintro; rfl
  · obtain ⟨rfl, hemp⟩ := hlog
    wp_apply os.model.wp_unlinkLoop_nofile d b R j dq (DFrac.own 1) _ qc hb
      (fun i hi => by rw [os.rmDir_cur_none] at hi; cases hi) $$ [Hp Hb Hperm]
      as %e ⟨%he, Hp, Hb, Hperm⟩
    · iframe; iframe #
    iapply HΦ
    iframe
    isplitr
    · ipureintro; exact he
    unfold rmAllOut
    iexists _, hJ'; iframe; isplitr
    · ipureintro; exact hsub
    iright; iexists x, s; iframe; ipureintro; exact ⟨rfl, hemp⟩

/-- `open` loop (read-only) on the directory `d/b` (the state `rmAllOut`): an error, or a shared
directory fd on `J`, `b` still `J`. -/
theorem os.model.wp_openLoop_dirSt (d b : GoString) (j J : Ino) (R : Roots) (qd : Qp)
    (h hJ0 : NamesH) (qc : Qp) (hb : NameOk b) (hJ : h.cur !! b = some (.dir J)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ rmAllOut j b J h hJ0 ∗
        osCallPerm qc }}
      (App (Val os.model.openLoop) (Val #(child d b)))
    {{ (fd e : w64), RET (PairV #fd #e); osPathS R d (DFrac.own qd) j ∗ osCallPerm qc ∗
        ((⌜e ≠ 0⌝ ∗ rmAllOut j b J h hJ0) ∨
         (⌜e = 0⌝ ∗ osDirFdS fd J .idle ∗ os.rmPresent j b J h hJ0)) }} := by
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hst, Hperm⟩ HΦ
  isimp only [rmAllOut] at Hst
  icases Hst with ⟨%h', %hJ', Hb, HJ, %hsub, Hor⟩
  icases Hor with (%hh | ⟨%x, %s, Hlog, %hlog⟩)
  · subst hh
    icases os.osPathS_borrow R d b j J qd h' hb hJ $$ [Hp Hb] with ⟨%ε, Hpc, Hback⟩
    · iframe
    wp_apply os.model.wp_openLoop_spine (child d b) R J (DFrac.own ε) qc $$ [Hpc Hperm]
      as %fd %e ⟨Hpc, Hperm, Ho⟩
    · iframe; iframe #
    icases Hback $$ Hpc with ⟨Hp, Hb⟩
    iapply HΦ
    iframe
    icases Ho with (%he | ⟨%he, Hfd⟩)
    · ileft
      isplitr
      · ipureintro; exact he
      unfold rmAllOut
      iexists h', hJ'; iframe; isplitr
      · ipureintro; exact hsub
      ileft; ipureintro; rfl
    · iright
      iframe
      isplitr
      · ipureintro; exact he
      unfold os.rmPresent
      iexists hJ'; iframe; ipureintro; exact hsub
  · obtain ⟨rfl, hemp⟩ := hlog
    wp_apply os.model.wp_openLoop_leaf d b R j (DFrac.own qd) (DFrac.own 1) _ qc hb
      (fun J' hi => by rw [os.rmDir_cur_none] at hi; cases hi) $$ [Hp Hb Hperm]
      as %fd %e ⟨Hp, Hb, Hperm, %hne, -⟩
    · iframe; iframe #
    iapply HΦ
    iframe
    ileft
    isplitr
    · ipureintro; exact hne (os.rmDir_cur_none _ _ _ _ _ _)
    unfold rmAllOut
    iexists _, hJ'; iframe; isplitr
    · ipureintro; exact hsub
    iright; iexists x, s; iframe; ipureintro; exact ⟨rfl, hemp⟩

end proof

end EtcdGrove
end Perennial
