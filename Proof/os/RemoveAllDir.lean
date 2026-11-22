/-
`os.RemoveAll`'s model on the directory it removes (`TrustedCode/os.lean`), in the tree's shared
mode, for `Proof/os/RemoveAll.lean`: the `unlink` loop on a name holding no file, and the `rmdir`
loop on the directory `d/b` (`J`) under the guard, over the state `rmAllOut` (the claims on `b` and
on `J`'s names; `b` as it was or its `rmdir` logged). Lean-first; untrusted.
-/
module

public import Proof.os.RemoveAllLeaf

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

/-- The entries after the removal of the name `c` (its claim `hc'` back from the claim
`hJ.restrict J (.only [c])`) and the merge, `h''`, are some of `hJ0`'s when `hJ`'s were. -/
theorem os.entsSub_merge1 {J : Ino} {c : GoString} {hJ hc' h'' : NamesH} {e0 : Ents}
    (hsub : EntsSub hJ.cur e0) (hlo : LeafOk c (hJ.restrict J (.only [c])) hc')
    (hm : h''.cur !! c = hc'.cur !! c ∧
      ∀ x, x ≠ c → h''.cur !! x = (hJ.restrict J (.except [c])).cur !! x) :
    EntsSub h''.cur e0 := by
  intro x n hx
  by_cases hxc : x = c
  · subst hxc
    rw [hm.1] at hx
    have := hlo.1 x n hx
    simp only [NamesH.restrict] at this
    exact hsub x n (EntsSub.restrictN _ _ x n this)
  · rw [hm.2 x hxc] at hx
    simp only [NamesH.restrict] at hx
    exact hsub x n (EntsSub.restrictN _ _ x n hx)

/-- The claim on `c` split off a directory's whole claim holds what the whole one did. -/
theorem os.restrict_only_cur (J : Ino) (c : GoString) (hJ : NamesH) :
    (hJ.restrict J (.only [c])).cur !! c = hJ.cur !! c := by
  simp only [NamesH.restrict]
  exact restrictN_lookup _ _ _ (by simp [NameSet.Mem])

/-- `unlink` loop on a name holding no file (a fraction of the claim on it): an errno, no
effect. -/
theorem os.model.wp_unlinkLoop_nofile (p c : GoString) (R : Roots) (J : Ino) (dq dqn : DFrac)
    (hc : NamesH) (qc : Qp) (hcN : NameOk c) (hnf : ∀ i, hc.cur !! c ≠ some (.file i)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗
        osNames J (.only [c]) dqn hc ∗ osCallPerm (callKey R p) qc }}
      (App (Val os.model.unlinkLoop) (Val #(child p c)))
    {{ (e : w64), RET #e; ⌜e ≠ 0⌝ ∗
        ⌜FsNoErrAt (child p c) → (∃ J', hc.cur !! c = some (.dir J')) → e = EISDIR⌝ ∗
        osPathS R p dq J ∗ osNames J (.only [c]) dqn hc ∗
        osCallPerm (callKey R p) qc }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm Hp Hn
  icases osCallPerm_child R p c _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  wp_apply +noauto wp_osCallBeginS R _ qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  wp_auto
  wp_apply +noauto wp_osUnlinkS_noneW R p c J dq dqn hc t s0 qc hcN hnf CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e %he %hw Hperm Hp Hn
  wp_auto
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    iapply IH $$ Hperm Hp Hn HΦ
  rw [decide_eq_false he4]
  wp_auto
  iapply HΦ
  iframe
  isplitr
  · ipureintro; exact he
  ipureintro; exact hw

/-- The name `b` after the `rmdir` of `J` was logged holds nothing. -/
theorem os.rmDir_cur_none (j : Ino) (b : GoString) (J : Ino) (h : NamesH) (x s : Nat) :
    (h.log x (rmDirEnt j b J s) (restrictN (.only [b]) (GMap.delete b h.cur))).cur !! b = none := by
  simp only [NamesH.log]
  rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem])]; exact GMap.lookup_delete _ _

/-- **`rmAllOut` whose first arm (`b` still `J`) also says `P`**: what the loops on `d/b` witness of
their errno while `b` is there (`FsNoErrAt`, `RemoveAllNE.lean`). -/
def os.rmAllOutP (j : Ino) (b : GoString) (J : Ino) (h hJ0 : NamesH) (P : Prop) : IProp GF :=
  iprop(∃ (h' hJ' : NamesH), osNames j (.only [b]) (DFrac.own 1) h' ∗
    osNames J (.except []) (DFrac.own 1) hJ' ∗ ⌜EntsSub hJ'.cur hJ0.cur⌝ ∗
    (⌜h' = h ∧ P⌝ ∨ ∃ x s, osLogged x (rmDirEnt j b J s) ∗
      ⌜h' = h.log x (rmDirEnt j b J s) (restrictN (.only [b]) (GMap.delete b h.cur)) ∧
        hJ'.cur = ∅⌝))

theorem os.rmAllOutP_out (j : Ino) (b : GoString) (J : Ino) (h hJ0 : NamesH) (P : Prop) :
    os.rmAllOutP (GF := GF) j b J h hJ0 P ⊢ rmAllOut j b J h hJ0 := by
  unfold os.rmAllOutP rmAllOut
  iintro ⟨%h', %hJ', Hb, HJ, %hsub, Ho⟩
  iexists h', hJ'
  iframe
  isplitr
  · ipureintro; exact hsub
  icases Ho with (%he | Ho)
  · ileft; ipureintro; exact he.1
  · iright; iexact Ho

theorem os.rmAllOutP_of (j : Ino) (b : GoString) (J : Ino) (h hJ0 : NamesH) (P : Prop) (hP : P) :
    rmAllOut (GF := GF) j b J h hJ0 ⊢ os.rmAllOutP j b J h hJ0 P := by
  unfold os.rmAllOutP rmAllOut
  iintro ⟨%h', %hJ', Hb, HJ, %hsub, Ho⟩
  iexists h', hJ'
  iframe
  isplitr
  · ipureintro; exact hsub
  icases Ho with (%he | Ho)
  · ileft; ipureintro; exact ⟨he, hP⟩
  · iright; iexact Ho

/-- `rmdir` loop on the directory `d/b` (`J`, the state `rmAllOut`), under the guard `t` (of a path
`pg` in `d`'s root's tree): an
errno; the state, perhaps with the `rmdir` logged (only on an empty `J`). -/
theorem os.model.wp_rmdirLoop_dirStW (d b : GoString) (j J : Ino) (R : Roots) (qd : Qp)
    (h hJ0 : NamesH) (q g : Qp) (t sg : Nat) (pg : GoString)
    (hkg : callKey R pg = callKey R (child d b)) (hb : NameOk b) (hJ : h.cur !! b = some (.dir J))
    (hqg : q + g = 1) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ rmAllOut j b J h hJ0 ∗
        osCallPerm (callKey R d) q ∗ osGuardS t sg pg g ∗ osLogLb sg }}
      (App (Val os.model.rmdirLoop) (Val #(child d b)))
    {{ (e : w64), RET #e; osPathS R d (DFrac.own qd) j ∗
        os.rmAllOutP j b J h hJ0 (FsNoErrAt (child d b) → e = ENOTEMPTY) ∗ osCallPerm (callKey R d) q ∗
        osGuardS t sg pg g }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hst, Hperm, Hg, #Hlsg⟩
  iloeb as IH generalizing Hperm Hp Hst Hg
  icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  wp_apply +noauto wp_osCallBeginS R _ q sg CoPset.subseteq_top CoPset.subseteq_top
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
      wp_apply +noauto wp_osRmdirS_nonemptyW R d b j J (.except []) (DFrac.own qd.half) (DFrac.own ε)
        (DFrac.own 1) hJ' c t1 s0 q hb (by simp [NameSet.Mem]) hc CoPset.subseteq_top
        CoPset.subseteq_top $$ Hos Hsi Hp2 Hpc HJ Hk as %e %he %hw Hperm Hp2 Hpc HJ
      icases Hback $$ Hpc with ⟨Hp1, Hb⟩
      ihave Hp := (osPathS_frac R d qd.half qd.half j).2 $$ [Hp1 Hp2]
      · iframe
      rw [Qp.half_add_half qd]
      ihave Hst : os.rmAllOutP j b J h' hJ0 (FsNoErrAt (child d b) → e = ENOTEMPTY) $$ [Hb HJ]
      · unfold os.rmAllOutP; iexists h', hJ'; iframe; isplitr
        · ipureintro; exact hsub
        ileft; ipureintro; exact ⟨rfl, hw⟩
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        ihave Hst := os.rmAllOutP_out _ _ _ _ _ _ $$ Hst
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
      wp_apply +noauto wp_osRmdirSGW R d b j J (DFrac.own qd) h' hJ' t1 s0 t sg pg q g hqg hs hkg hb hJ hemp
        CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hb HJ Hk Hg
        as %e %hw Hperm Hg Hp HJ Hres
      unfold osNamesAfter
      ihave Hst : os.rmAllOutP j b J h' hJ0 (FsNoErrAt (child d b) → e = ENOTEMPTY) $$ [Hres HJ]
      · unfold os.rmAllOutP
        icases Hres with (⟨%he, Hb⟩ | ⟨%x, Hlog, Hb⟩)
        · iexists h', hJ'; iframe; isplitr
          · ipureintro; exact hsub
          ileft; ipureintro; exact ⟨rfl, fun hne => absurd (hw hne) he⟩
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
        ihave Hst := os.rmAllOutP_out _ _ _ _ _ _ $$ Hst
        iapply IH $$ Hperm Hp Hst Hg HΦ
      rw [decide_eq_false he4]
      wp_auto
      iapply HΦ
      iframe
  · obtain ⟨rfl, hemp⟩ := hlog
    wp_apply +noauto wp_osRmdirS_none R d b j (DFrac.own qd) (DFrac.own 1) _ t1 s0 q hb
      (fun J' h'' => by rw [os.rmDir_cur_none] at h''; cases h'') CoPset.subseteq_top
      CoPset.subseteq_top $$ Hos Hsi Hp Hb Hk as %e %he Hperm Hp Hb
    ihave Hst : os.rmAllOutP j b J h hJ0 (FsNoErrAt (child d b) → e = ENOTEMPTY) $$ [Hb HJ Hlog]
    · unfold os.rmAllOutP; iexists _, hJ'; iframe; isplitr
      · ipureintro; exact hsub
      iright; iexists x, s
      isplitl
      · iexact Hlog
      ipureintro; exact ⟨rfl, hemp⟩
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      ihave Hst := os.rmAllOutP_out _ _ _ _ _ _ $$ Hst
      iapply IH $$ Hperm Hp Hst Hg HΦ
    rw [decide_eq_false he4]
    wp_auto
    iapply HΦ
    iframe

theorem os.model.wp_rmdirLoop_dirSt (d b : GoString) (j J : Ino) (R : Roots) (qd : Qp)
    (h hJ0 : NamesH) (q g : Qp) (t sg : Nat) (pg : GoString)
    (hkg : callKey R pg = callKey R (child d b)) (hb : NameOk b) (hJ : h.cur !! b = some (.dir J))
    (hqg : q + g = 1) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ rmAllOut j b J h hJ0 ∗
        osCallPerm (callKey R d) q ∗ osGuardS t sg pg g ∗ osLogLb sg }}
      (App (Val os.model.rmdirLoop) (Val #(child d b)))
    {{ (e : w64), RET #e; osPathS R d (DFrac.own qd) j ∗ rmAllOut j b J h hJ0 ∗ osCallPerm (callKey R d) q ∗
        osGuardS t sg pg g }} := by
  iintro %Φ Hpre HΦ
  wp_apply os.model.wp_rmdirLoop_dirStW d b j J R qd h hJ0 q g t sg pg hkg hb hJ hqg $$ Hpre
    as %e ⟨Hp, Hst, Hperm, Hg⟩
  iapply HΦ
  iframe
  iapply os.rmAllOutP_out $$ Hst

/-- `open` loop (read-only) of the directory `j` (a spine to it): an error, or a shared directory
fd on it. -/
theorem os.model.wp_openLoop_spineW (p : GoString) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq j ∗ osCallPerm (callKey R p) qc }}
      (App (Val os.model.openLoop) (Val #p))
    {{ (fd e : w64), RET (PairV #fd #e); osPathS R p dq j ∗ osCallPerm (callKey R p) qc ∗
        (⌜e ≠ 0 ∧ e ≠ 2⌝ ∨ ⌜e = 0⌝ ∗ osDirFdS fd j .idle) }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm⟩
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm Hp
  wp_apply +noauto wp_osCallBeginS R _ qc 0 CoPset.subseteq_top CoPset.subseteq_top
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
    ileft; ipureintro
    refine ⟨he0, fun h2 => ?_⟩
    rcases hres with ⟨h0, -⟩ | ⟨-, hen, -⟩
    · exact he0 h0
    · exact hen h2

theorem os.model.wp_openLoop_spine (p : GoString) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq j ∗ osCallPerm (callKey R p) qc }}
      (App (Val os.model.openLoop) (Val #p))
    {{ (fd e : w64), RET (PairV #fd #e); osPathS R p dq j ∗ osCallPerm (callKey R p) qc ∗
        (⌜e ≠ 0⌝ ∨ ⌜e = 0⌝ ∗ osDirFdS fd j .idle) }} := by
  iintro %Φ Hpre HΦ
  wp_apply os.model.wp_openLoop_spineW p R j dq qc $$ Hpre as %fd %e ⟨Hp, Hperm, Ho⟩
  iapply HΦ
  iframe
  icases Ho with (%he | Ho)
  · ileft; ipureintro; exact he.1
  · iright; iexact Ho

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
theorem os.model.wp_unlinkLoop_dirStW (d b : GoString) (j J : Ino) (R : Roots) (dq : DFrac)
    (h hJ0 : NamesH) (qc : Qp) (hb : NameOk b) (hJ : h.cur !! b = some (.dir J)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ rmAllOut j b J h hJ0 ∗
        osCallPerm (callKey R d) qc }}
      (App (Val os.model.unlinkLoop) (Val #(child d b)))
    {{ (e : w64), RET #e; ⌜e ≠ 0⌝ ∗ osPathS R d dq j ∗
        os.rmAllOutP j b J h hJ0 (FsNoErrAt (child d b) → e = EISDIR) ∗ osCallPerm (callKey R d) qc }} := by
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hst, Hperm⟩ HΦ
  isimp only [rmAllOut] at Hst
  icases Hst with ⟨%h', %hJ', Hb, HJ, %hsub, Hor⟩
  icases Hor with (%hh | ⟨%x, %s, Hlog, %hlog⟩)
  · subst hh
    wp_apply os.model.wp_unlinkLoop_nofile d b R j dq (DFrac.own 1) h' qc hb
      (fun i hi => by rw [hJ] at hi; cases hi) $$ [Hp Hb Hperm] as %e ⟨%he, %hw, Hp, Hb, Hperm⟩
    · iframe; iframe #
    iapply HΦ
    iframe
    isplitr
    · ipureintro; exact he
    unfold os.rmAllOutP
    iexists h', hJ'; iframe; isplitr
    · ipureintro; exact hsub
    ileft; ipureintro; exact ⟨rfl, fun hne => hw hne ⟨J, hJ⟩⟩
  · obtain ⟨rfl, hemp⟩ := hlog
    wp_apply os.model.wp_unlinkLoop_nofile d b R j dq (DFrac.own 1) _ qc hb
      (fun i hi => by rw [os.rmDir_cur_none] at hi; cases hi) $$ [Hp Hb Hperm]
      as %e ⟨%he, %hw, Hp, Hb, Hperm⟩
    · iframe; iframe #
    iapply HΦ
    iframe
    isplitr
    · ipureintro; exact he
    unfold os.rmAllOutP
    iexists _, hJ'; iframe; isplitr
    · ipureintro; exact hsub
    iright; iexists x, s; iframe; ipureintro; exact ⟨rfl, hemp⟩

theorem os.model.wp_unlinkLoop_dirSt (d b : GoString) (j J : Ino) (R : Roots) (dq : DFrac)
    (h hJ0 : NamesH) (qc : Qp) (hb : NameOk b) (hJ : h.cur !! b = some (.dir J)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ rmAllOut j b J h hJ0 ∗
        osCallPerm (callKey R d) qc }}
      (App (Val os.model.unlinkLoop) (Val #(child d b)))
    {{ (e : w64), RET #e; ⌜e ≠ 0⌝ ∗ osPathS R d dq j ∗ rmAllOut j b J h hJ0 ∗ osCallPerm (callKey R d) qc }} := by
  iintro %Φ Hpre HΦ
  wp_apply os.model.wp_unlinkLoop_dirStW d b j J R dq h hJ0 qc hb hJ $$ Hpre as %e ⟨%he, Hp, Hst, Hperm⟩
  iapply HΦ
  iframe
  isplitr
  · ipureintro; exact he
  iapply os.rmAllOutP_out $$ Hst

/-- `open` loop (read-only) on the directory `d/b` (the state `rmAllOut`): an error, or a shared
directory fd on `J`, `b` still `J`. -/
theorem os.model.wp_openLoop_dirStW (d b : GoString) (j J : Ino) (R : Roots) (qd : Qp)
    (h hJ0 : NamesH) (qc : Qp) (hb : NameOk b) (hJ : h.cur !! b = some (.dir J)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ rmAllOut j b J h hJ0 ∗
        osCallPerm (callKey R d) qc }}
      (App (Val os.model.openLoop) (Val #(child d b)))
    {{ (fd e : w64), RET (PairV #fd #e); osPathS R d (DFrac.own qd) j ∗ osCallPerm (callKey R d) qc ∗
        ((⌜e ≠ 0⌝ ∗ os.rmAllOutP j b J h hJ0 (e ≠ 2)) ∨
         (⌜e = 0⌝ ∗ osDirFdS fd J .idle ∗ os.rmPresent j b J h hJ0)) }} := by
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hst, Hperm⟩ HΦ
  isimp only [rmAllOut] at Hst
  icases Hst with ⟨%h', %hJ', Hb, HJ, %hsub, Hor⟩
  icases Hor with (%hh | ⟨%x, %s, Hlog, %hlog⟩)
  · subst hh
    icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
    icases os.osPathS_borrow R d b j J qd h' hb hJ $$ [Hp Hb] with ⟨%ε, Hpc, Hback⟩
    · iframe
    wp_apply os.model.wp_openLoop_spineW (child d b) R J (DFrac.own ε) qc $$ [Hpc Hperm]
      as %fd %e ⟨Hpc, Hperm, Ho⟩
    · iframe; iframe #
    icases Hback $$ Hpc with ⟨Hp, Hb⟩
    icases osCallPerm_unchild R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
    iapply HΦ
    iframe
    icases Ho with (%he | ⟨%he, Hfd⟩)
    · ileft
      isplitr
      · ipureintro; exact he.1
      unfold os.rmAllOutP
      iexists h', hJ'; iframe; isplitr
      · ipureintro; exact hsub
      ileft; ipureintro; exact ⟨rfl, he.2⟩
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
    unfold os.rmAllOutP
    iexists _, hJ'; iframe; isplitr
    · ipureintro; exact hsub
    iright; iexists x, s; iframe; ipureintro; exact ⟨rfl, hemp⟩

theorem os.model.wp_openLoop_dirSt (d b : GoString) (j J : Ino) (R : Roots) (qd : Qp)
    (h hJ0 : NamesH) (qc : Qp) (hb : NameOk b) (hJ : h.cur !! b = some (.dir J)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ rmAllOut j b J h hJ0 ∗
        osCallPerm (callKey R d) qc }}
      (App (Val os.model.openLoop) (Val #(child d b)))
    {{ (fd e : w64), RET (PairV #fd #e); osPathS R d (DFrac.own qd) j ∗ osCallPerm (callKey R d) qc ∗
        ((⌜e ≠ 0⌝ ∗ rmAllOut j b J h hJ0) ∨
         (⌜e = 0⌝ ∗ osDirFdS fd J .idle ∗ os.rmPresent j b J h hJ0)) }} := by
  iintro %Φ Hpre HΦ
  wp_apply os.model.wp_openLoop_dirStW d b j J R qd h hJ0 qc hb hJ $$ Hpre as %fd %e ⟨Hp, Hperm, Ho⟩
  iapply HΦ
  iframe
  icases Ho with (⟨%he, Hst⟩ | Ho)
  · ileft
    isplitr
    · ipureintro; exact he
    iapply os.rmAllOutP_out $$ Hst
  · iright; iexact Ho

end proof

end EtcdGrove
end Perennial
