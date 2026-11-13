/-
`os.RemoveAll`'s model on an entry of the directory it removes (`TrustedCode/os.lean`,
`model.removeAllFrom` on a name holding a file or nothing), in the tree's shared mode, for
`Proof/os/RemoveAll.lean`: the `unlink`, `open` and `rmdir` loops on such a name, and the whole
`removeAllFrom` on it, which never reaches the passes' reads (an fd of a file is closed, `FdKind`).
Lean-first; untrusted.
-/
module

public import LinuxFs.Proof.os.RemoveAllParts
public import LinuxFs.Proof.os.RemoveAllExt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

theorem EntsSub.trans {a b c : Ents} (h1 : EntsSub a b) (h2 : EntsSub b c) : EntsSub a c :=
  fun x n h => h2 x n (h1 x n h)

theorem EntsSub.refl (a : Ents) : EntsSub a a := fun _ _ h => h

theorem EntsSub.restrictN (N : NameSet) (e : Ents) : EntsSub (Fs.restrictN N e) e := by
  intro y m hy
  by_cases hN : N.Mem y
  · rwa [restrictN_lookup _ _ _ hN] at hy
  · rw [restrictN_lookup_not _ _ _ hN] at hy; cases hy

theorem EntsSub.delete (b : GoString) (e : Ents) : EntsSub (GMap.delete b e) e := by
  intro y m hy
  exact ((GMap.lookup_delete_Some e b y m).1 hy).2

theorem EntsSub.restrictN_delete {N : NameSet} {b : GoString} {e e0 : Ents} (h : EntsSub e e0) :
    EntsSub (Fs.restrictN N (GMap.delete b e)) e0 :=
  ((EntsSub.restrictN N _).trans (EntsSub.delete b e)).trans h

/-- The claim on `c` after a removal of `c` (from `hc`): its entries a part of what they were,
unchanged if `c` held nothing. -/
def LeafOk (c : GoString) (hc hc' : NamesH) : Prop :=
  EntsSub hc'.cur hc.cur ∧ (hc.cur !! c = none → hc' = hc)

theorem LeafOk.refl (c : GoString) (hc : NamesH) : LeafOk c hc hc :=
  ⟨EntsSub.refl _, fun _ => rfl⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.fileStat.FieldAssumptions]

/-- `unlink` loop on a name holding a file or nothing (the whole claim on it): some errno; the
claim's entries a part of what they were. -/
theorem os.model.wp_unlinkLoop_leaf (p c : GoString) (R : Roots) (J : Ino) (dq dqn : DFrac)
    (hc : NamesH) (qc : Qp) (hcN : NameOk c) (hcf : ∀ J', hc.cur !! c ≠ some (.dir J'))
    (hw : dqn = DFrac.own 1 ∨ hc.cur !! c = none) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗
        osNames J (.only [c]) dqn hc ∗ osCallPerm qc }}
      (App (Val os.model.unlinkLoop) (Val #(child p c)))
    {{ (e : w64), RET #e; osPathS R p dq J ∗ osCallPerm qc ∗
        ∃ hc', osNames J (.only [c]) dqn hc' ∗ ⌜LeafOk c hc hc'⌝ }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  have hcN' : (NameSet.only [c]).Mem c := by simp [NameSet.Mem]
  ihave Hst : (∃ hc', osNames J (.only [c]) dqn hc' ∗ ⌜LeafOk c hc hc'⌝ : IProp GF)
    $$ [Hn]
  · iexists hc; iframe; ipureintro; exact LeafOk.refl c hc
  iloeb as IH generalizing Hperm Hp Hst
  icases Hst with ⟨%hc', Hn, %hsub⟩
  imod osNames_next R J _ _ hc' CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  wp_apply +noauto wp_osCallBeginS R qc hc'.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  wp_auto
  rcases hcur : hc'.cur !! c with _ | n
  · wp_apply +noauto wp_osUnlinkS_none R p c J dq dqn hc' t s0 qc hcN
      (fun i h => by rw [hcur] at h; cases h) CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ Hperm Hp [Hn] HΦ
      iexists hc'; iframe; ipureintro; exact hsub
    rw [decide_eq_false he4]
    wp_auto
    iapply HΦ
    iframe
    ipureintro; exact hsub
  · obtain ⟨i, rfl⟩ : ∃ i, n = .file i := by
      cases n with
      | file i => exact ⟨i, rfl⟩
      | dir J' => exact absurd (hsub.1 c _ hcur) (hcf J')
    have hfile : hc.cur !! c = some (.file i) := hsub.1 c _ hcur
    obtain rfl : dqn = DFrac.own 1 := by
      rcases hw with h | h
      · exact h
      · rw [hfile] at h; cases h
    wp_apply +noauto wp_osUnlinkS R p c J i dq hc' t s0 qc hcN hcur hs CoPset.subseteq_top
      CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e Hperm Hp Hres
    unfold osNamesAfter
    ihave Hst : (∃ hc'', osNames J (.only [c]) (DFrac.own 1) hc'' ∗ ⌜LeafOk c hc hc''⌝ :
        IProp GF) $$ [Hres]
    · icases Hres with (⟨-, Hn⟩ | ⟨%x, -, Hn⟩)
      · iexists hc'; iframe; ipureintro; exact hsub
      · iexists _; iframe; ipureintro
        refine ⟨EntsSub.restrictN_delete hsub.1, fun h => ?_⟩
        rw [hfile] at h; cases h
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ Hperm Hp Hst HΦ
    rw [decide_eq_false he4]
    wp_auto
    iapply HΦ
    iframe

theorem os.flRO_ok : OpenFlagsOk flRO.toNat ∧ flRO.toNat / O_TRUNC % 2 = 0 ∧
    flRO.toNat / O_CREAT % 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold OpenFlagsOk; decide
  · decide
  · decide

/-- `open` loop (read-only) on a name holding a file or nothing (a fraction of the claim on it):
an error, or an fd of the file. -/
theorem os.model.wp_openLoop_leaf (p c : GoString) (R : Roots) (J : Ino) (dq dqn : DFrac)
    (hc : NamesH) (qc : Qp) (hcN : NameOk c) (hcf : ∀ J', hc.cur !! c ≠ some (.dir J')) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗
        osNames J (.only [c]) dqn hc ∗ osCallPerm qc }}
      (App (Val os.model.openLoop) (Val #(child p c)))
    {{ (fd e : w64), RET (PairV #fd #e); osPathS R p dq J ∗ osNames J (.only [c]) dqn hc ∗
        osCallPerm qc ∗
        (⌜e ≠ 0⌝ ∨ ⌜e = 0⌝ ∗ ∃ i, osFd fd (DFrac.own 1) (openFd i flRO)) }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  have hcN' : (NameSet.only [c]).Mem c := by simp [NameSet.Mem]
  obtain ⟨hfl, htr, hcr⟩ := os.flRO_ok
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm Hp Hn
  wp_apply +noauto wp_osCallBeginS R qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  wp_auto
  rcases hcur : hc.cur !! c with _ | n
  · wp_apply +noauto wp_osOpenAbsentS R p c J (.only [c]) dq dqn hc t s0 qc flRO hfl hcr htr hcN
      hcN' hcur CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ Hperm Hp Hn HΦ
    rw [decide_eq_false he4]
    wp_auto
    iapply HΦ
    iframe
    ileft; ipureintro; exact he
  · obtain ⟨i, rfl⟩ : ∃ i, n = .file i := by
      cases n with
      | file i => exact ⟨i, rfl⟩
      | dir J' => exact absurd hcur (hcf J')
    wp_apply +noauto wp_osOpenFileS R p c J i (.only [c]) dq dqn hc t s0 qc flRO hfl htr hcN hcN'
      hcur CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk
      as %fd %e %hres Hperm Hp Hn Hfd
    wp_auto
    by_cases he0 : e = W64 0
    · subst he0
      ihave Hfd := (show (if W64 0 = (0 : w64) then osFd (GF := GF) fd (DFrac.own 1)
          (openFd i flRO) else emp) ⊢ osFd fd (DFrac.own 1) (openFd i flRO)
        by split
           · iintro H; iexact H
           · exact absurd rfl ‹_›) $$ Hfd
      rw [decide_eq_false (show W64 0 ≠ W64 4 by decide)]
      wp_auto
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; rfl
      iexists i; iframe
    · iclear Hfd
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        iapply IH $$ Hperm Hp Hn HΦ
      rw [decide_eq_false he4]
      wp_auto
      iapply HΦ
      iframe
      ileft; ipureintro; exact he0

/-- `rmdir` loop on a name holding no directory (a fraction of the claim on it): an errno. -/
theorem os.model.wp_rmdirLoop_none (p c : GoString) (R : Roots) (J : Ino) (dq dqn : DFrac)
    (hc : NamesH) (qc : Qp) (hcN : NameOk c) (hcf : ∀ J', hc.cur !! c ≠ some (.dir J')) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗
        osNames J (.only [c]) dqn hc ∗ osCallPerm qc }}
      (App (Val os.model.rmdirLoop) (Val #(child p c)))
    {{ (e : w64), RET #e; ⌜e ≠ 0⌝ ∗ osPathS R p dq J ∗ osNames J (.only [c]) dqn hc ∗
        osCallPerm qc }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm Hp Hn
  wp_apply +noauto wp_osCallBeginS R qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  wp_auto
  wp_apply +noauto wp_osRmdirS_none R p c J dq dqn hc t s0 qc hcN hcf CoPset.subseteq_top
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

theorem os.model.wp_removeAllFrom_leaf (p c : GoString) (R : Roots) (J : Ino) (dq dqn : DFrac)
    (hc : NamesH) (qc : Qp) (hcN : NameOk c) (hcf : ∀ J', hc.cur !! c ≠ some (.dir J'))
    (hw : dqn = DFrac.own 1 ∨ hc.cur !! c = none) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗
        osNames J (.only [c]) dqn hc ∗ osCallPerm qc }}
      (App (App (Val os.model.removeAllFrom) (Val #p)) (Val #c))
    {{ (pe : Loc), RET #pe; osPathS R p dq J ∗ osCallPerm qc ∗ os.peOk pe ∗
        ∃ hc', osNames J (.only [c]) dqn hc' ∗ ⌜LeafOk c hc hc'⌝ }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  rw [show p ++ [47#8] ++ c = child p c by simp [child, slashB]]
  wp_apply os.model.wp_unlinkLoop_leaf p c R J dq dqn hc qc hcN hcf hw $$ [Hp Hn Hperm]
    as %e ⟨Hp, Hperm, %hc', Hn, %hsub⟩
  · iframe; iframe #
  have hcf' : ∀ J', hc'.cur !! c ≠ some (.dir J') := fun J' h => hcf J' (hsub.1 c _ h)
  by_cases he0 : e = W64 0
  · rw [decide_eq_true he0]
    wp_auto
    iapply HΦ
    iframe
    isplitr
    · iapply os.peOk_null
    ipureintro; exact hsub
  rw [decide_eq_false he0]
  wp_auto
  by_cases he2 : e = W64 2
  · rw [decide_eq_true he2]
    wp_auto
    iapply HΦ
    iframe
    isplitr
    · iapply os.peOk_null
    ipureintro; exact hsub
  rw [decide_eq_false he2]
  wp_auto
  by_cases hcls : ¬ (e = W64 21 ∨ e = W64 1 ∨ e = W64 13)
  · simp only [not_or] at hcls
    obtain ⟨h21, h1, h13⟩ := hcls
    simp only [decide_eq_false h21, Bool.not_false]
    wp_auto
    simp only [decide_eq_false h1, Bool.not_false]
    wp_auto
    simp only [decide_eq_false h13, Bool.not_false]
    wp_auto
    wp_apply os.model.wp_pathErrorPtr_errno _ _ e he0 as %pe Hpe
    iapply HΦ
    iframe
    ipureintro; exact hsub
  rw [Classical.not_not] at hcls
  have he0' := he0
  clear he0 he2
  rcases hcls with rfl | rfl | rfl <;> wp_auto
  all_goals
    wp_apply os.model.wp_openLoop_leaf p c R J dq dqn hc' qc hcN hcf' $$ [Hp Hn Hperm]
      as %fd %e' ⟨Hp, Hn, Hperm, Hr⟩
    · iframe; iframe #
    icases Hr with (%he' | ⟨%he', %i, Hfd⟩)
    · simp only [decide_eq_false (show e' ≠ W64 0 from he'), Bool.not_false]
      wp_auto
      by_cases he'2 : e' = W64 2
      · rw [decide_eq_true he'2]
        wp_auto
        iapply HΦ
        iframe
        isplitr
        · iapply os.peOk_null
        ipureintro; exact hsub
      rw [decide_eq_false he'2]
      try wp_auto
      by_cases he'20 : e' = W64 20
      · rw [decide_eq_true he'20]
        try wp_auto
        wp_apply os.model.wp_pathErrorPtr_errno _ _ _ he0' as %pe Hpe
        try wp_auto
        iapply HΦ
        iframe
        ipureintro; exact hsub
      rw [decide_eq_false he'20]
      try wp_auto
      wp_apply os.model.wp_pathErrorPtr_errno _ _ _ he' as %pe Hpe
      try wp_auto
      wp_apply os.model.wp_rmdirLoop_none p c R J dq dqn hc' qc hcN hcf'
        $$ [Hp Hn Hperm] as %e4 ⟨%he4, Hp, Hn, Hperm⟩
      · iframe; iframe #
      try wp_auto
      rw [decide_eq_false (show e4 ≠ W64 0 from he4)]
      try wp_auto
      by_cases he42 : e4 = W64 2
      · rw [decide_eq_true he42]
        try wp_auto
        iapply HΦ
        iframe
        isplitr
        · iapply os.peOk_null
        ipureintro; exact hsub
      rw [decide_eq_false he42]
      try wp_auto
      by_cases hpn : pe = null
      · simp only [decide_eq_true hpn, Bool.not_true]
        try wp_auto
        wp_apply os.model.wp_pathErrorPtr_errno _ _ _ he4 as %pe' Hpe'
        iapply HΦ
        iframe
        ipureintro; exact hsub
      · simp only [decide_eq_false hpn, Bool.not_false]
        try wp_auto
        iapply HΦ
        iframe
        ipureintro; exact hsub
    · simp only [decide_eq_true (show e' = W64 0 from he'), Bool.not_true]
      try wp_auto
      wp_apply wp_osFdKind fd (DFrac.own 1) _ CoPset.subseteq_top $$ Hos Hfd as Hfd
      wp_apply wp_osClose fd _ CoPset.subseteq_top $$ [Hfd] as %ec -
      · iframe; iframe #
      wp_apply os.model.wp_pathErrorPtr_errno _ _ _ he0' as %pe Hpe
      try wp_auto
      iapply HΦ
      iframe
      ipureintro; exact hsub

end proof

end EtcdGrove
end Perennial
