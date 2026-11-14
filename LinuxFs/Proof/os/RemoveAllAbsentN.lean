/-
The proof of `os.RemoveAll.specAbsentN` (stated in
`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/CreateCallees.lean`): `os.RemoveAll(d/b)` of an
absent `b`, with a fraction of a claim on any names `N` containing `b` (`RemoveAll.lean`'s
`specAbsentS` takes `.only [b]`). The proof is `specAbsentS`'s over the absent case of
`RemoveAllLeaf.lean`'s loops, restated for `N`; on an absent name each step only ends its call, so the
claim is unchanged (2026-11-14).

* `Fs.wp_osUnlinkAbsentSN`, `Fs.wp_osRmdirAbsentSN`: `unlink(2)`/`rmdir(2)` of an absent name with a
  fraction of a claim on names containing it: an errno, no effect (the extension's
  `wp_osUnlinkS_none'`/`wp_osRmdirS_none'`, which take `.only [b]`, for any `N ∋ b`; they belong in
  `GooseLang/Ext/Fs/TreeSharedCallEnd.lean`, as `SharedExt.lean`'s steps do).
* `os.model.wp_{unlinkLoop,openLoop,rmdirLoop,removeAllFrom}_absentN`: the model's loops on such a name.

Lean-first; untrusted.
-/
module

public import LinuxFs.Proof.os.RemoveAll
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.CreateCallees

@[expose] public section

noncomputable section

namespace Perennial

namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **`unlink(2)` of `d/b`, a name holding nothing**, with a fraction of a claim on names
containing `b`: an errno, no effect. -/
theorem wp_osUnlinkAbsentSN (R : Roots) (d b : GoString) (j : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (k s0 : Nat) (q : Qp) (hb : NameOk b) (hN : N.Mem b) (hi : h.cur !! b = none)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j N dqn h -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Unlink" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j N h →
      ∃ e', IsFsStep "Unlink" (PairV (osTokV k) (#(child d b))) st e' (st.metaEnd k) :=
    fun st _ _ hcall hp => ⟨_, child d b, k, s0, rfl, treeName_child hp.1 hb, hcall,
      Or.inr ⟨1, by decide, rfl, rfl⟩⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j N h →
      IsFsStep "Unlink" (PairV (osTokV k) (#(child d b))) st e' st' →
      st' = st.metaEnd k ∧ ∃ w, e' = Val w ∧ ∃ e : w64, e ≠ 0 ∧ w = #e := by
    intro st e' st' hw _ _ hp Hst
    simp only [IsFsStep] at Hst
    obtain ⟨p', k', s', hv, -, -, hres⟩ := Hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    rcases hres with ⟨i, -, -, hl, -⟩ | ⟨e, he0, rfl, rfl⟩
    · rw [pathNames_child hw hp hb hN, hi] at hl; cases hl
    · exact ⟨rfl, _, rfl, e, he0, rfl⟩
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_callEndS "Unlink" _ (by simp [val.isPanic]) R k s0 q
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j N dqn h)
    (fun st => PathNames st d j N h) (fun w => ∃ e : w64, e ≠ 0 ∧ w = #e)
    (fun st Γn hR hcoh => pathNames_of R d dq j _ dqn h st Γn hR hcoh) hprog hpost hE hE' Φ
    $$ Hinv Hsi [Hp Hn] Hk
  · isplitl [Hp]
    · iexact Hp
    · iexact Hn
  iintro %w %hW Hq ⟨Hp, Hn⟩
  obtain ⟨e, he, rfl⟩ := hW
  iapply HΦ $$ %e %he Hq Hp Hn

/-- **`rmdir(2)` of `d/b`, a name holding nothing**, with a fraction of a claim on names
containing `b`: an errno, no effect. -/
theorem wp_osRmdirAbsentSN (R : Roots) (d b : GoString) (j : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (k s0 : Nat) (q : Qp) (hb : NameOk b) (hN : N.Mem b) (hi : h.cur !! b = none)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j N dqn h -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rmdir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j N h →
      ∃ e', IsFsStep "Rmdir" (PairV (osTokV k) (#(child d b))) st e' (st.metaEnd k) :=
    fun st _ _ hcall hp => ⟨_, child d b, k, s0, rfl, treeName_child hp.1 hb, hcall,
      Or.inr ⟨1, by decide, rfl, rfl⟩⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j N h →
      IsFsStep "Rmdir" (PairV (osTokV k) (#(child d b))) st e' st' →
      st' = st.metaEnd k ∧ ∃ w, e' = Val w ∧ ∃ e : w64, e ≠ 0 ∧ w = #e := by
    intro st e' st' hw _ _ hp Hst
    simp only [IsFsStep] at Hst
    obtain ⟨p', k', s', hv, -, -, hres⟩ := Hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    rcases hres with ⟨J, -, -, ⟨hl, -⟩, -⟩ | ⟨e, he0, rfl, rfl⟩
    · rw [pathNames_child hw hp hb hN, hi] at hl; cases hl
    · exact ⟨rfl, _, rfl, e, he0, rfl⟩
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_callEndS "Rmdir" _ (by simp [val.isPanic]) R k s0 q
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j N dqn h)
    (fun st => PathNames st d j N h) (fun w => ∃ e : w64, e ≠ 0 ∧ w = #e)
    (fun st Γn hR hcoh => pathNames_of R d dq j _ dqn h st Γn hR hcoh) hprog hpost hE hE' Φ
    $$ Hinv Hsi [Hp Hn] Hk
  · isplitl [Hp]
    · iexact Hp
    · iexact Hn
  iintro %w %hW Hq ⟨Hp, Hn⟩
  obtain ⟨e, he, rfl⟩ := hW
  iapply HΦ $$ %e %he Hq Hp Hn

end specs

end Fs

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.fileStat.FieldAssumptions]

/-- `unlink` loop on an absent name (a fraction of a claim on names containing it): an errno. -/
theorem os.model.wp_unlinkLoop_absentN (p c : GoString) (R : Roots) (J : Ino) (N : NameSet)
    (dq dqn : DFrac) (hc : NamesH) (qc : Qp) (hcN : NameOk c) (hN : N.Mem c)
    (hn : hc.cur !! c = none) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗ osNames J N dqn hc ∗ osCallPerm qc }}
      (App (Val os.model.unlinkLoop) (Val #(child p c)))
    {{ (e : w64), RET #e; ⌜e ≠ 0⌝ ∗ osPathS R p dq J ∗ osNames J N dqn hc ∗ osCallPerm qc }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm Hp Hn
  wp_apply +noauto wp_osCallBeginS R qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  wp_auto
  wp_apply +noauto wp_osUnlinkAbsentSN R p c J N dq dqn hc t s0 qc hcN hN hn CoPset.subseteq_top
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

/-- `open` loop (read-only) on an absent name (a fraction of a claim on names containing it): an
errno. -/
theorem os.model.wp_openLoop_absentN (p c : GoString) (R : Roots) (J : Ino) (N : NameSet)
    (dq dqn : DFrac) (hc : NamesH) (qc : Qp) (hcN : NameOk c) (hN : N.Mem c)
    (hn : hc.cur !! c = none) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗ osNames J N dqn hc ∗ osCallPerm qc }}
      (App (Val os.model.openLoop) (Val #(child p c)))
    {{ (fd e : w64), RET (PairV #fd #e); ⌜e ≠ 0⌝ ∗ osPathS R p dq J ∗ osNames J N dqn hc ∗
        osCallPerm qc }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  obtain ⟨hfl, htr, hcr⟩ := os.flRO_ok
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm Hp Hn
  wp_apply +noauto wp_osCallBeginS R qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  wp_auto
  wp_apply +noauto wp_osOpenAbsentS R p c J N dq dqn hc t s0 qc flRO hfl hcr htr hcN
    hN hn CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
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

/-- `rmdir` loop on an absent name (a fraction of a claim on names containing it): an errno. -/
theorem os.model.wp_rmdirLoop_absentN (p c : GoString) (R : Roots) (J : Ino) (N : NameSet)
    (dq dqn : DFrac) (hc : NamesH) (qc : Qp) (hcN : NameOk c) (hN : N.Mem c)
    (hn : hc.cur !! c = none) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗ osNames J N dqn hc ∗ osCallPerm qc }}
      (App (Val os.model.rmdirLoop) (Val #(child p c)))
    {{ (e : w64), RET #e; ⌜e ≠ 0⌝ ∗ osPathS R p dq J ∗ osNames J N dqn hc ∗ osCallPerm qc }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm Hp Hn
  wp_apply +noauto wp_osCallBeginS R qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  wp_auto
  wp_apply +noauto wp_osRmdirAbsentSN R p c J N dq dqn hc t s0 qc hcN hN hn CoPset.subseteq_top
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

/-- `removeAllFrom(p, c)` on an absent name (a fraction of a claim on names containing it): an
error pointer, nothing changed. -/
theorem os.model.wp_removeAllFrom_absentN (p c : GoString) (R : Roots) (J : Ino) (N : NameSet)
    (dq dqn : DFrac) (hc : NamesH) (qc : Qp) (hcN : NameOk c) (hN : N.Mem c)
    (hn : hc.cur !! c = none) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗ osNames J N dqn hc ∗ osCallPerm qc }}
      (App (App (Val os.model.removeAllFrom) (Val #p)) (Val #c))
    {{ (pe : Loc), RET #pe; osPathS R p dq J ∗ osCallPerm qc ∗ os.peOk pe ∗
        osNames J N dqn hc }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  rw [show p ++ [47#8] ++ c = child p c by simp [child, slashB]]
  wp_apply os.model.wp_unlinkLoop_absentN p c R J N dq dqn hc qc hcN hN hn $$ [Hp Hn Hperm]
    as %e ⟨%he0, Hp, Hn, Hperm⟩
  · iframe; iframe #
  rw [decide_eq_false (show e ≠ W64 0 from he0)]
  wp_auto
  by_cases he2 : e = W64 2
  · rw [decide_eq_true he2]
    wp_auto
    iapply HΦ
    iframe
    iapply os.peOk_null
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
  rw [Classical.not_not] at hcls
  have he0' := he0
  clear he0 he2
  rcases hcls with rfl | rfl | rfl <;> wp_auto
  all_goals
    wp_apply os.model.wp_openLoop_absentN p c R J N dq dqn hc qc hcN hN hn $$ [Hp Hn Hperm]
      as %fd %e' ⟨%he', Hp, Hn, Hperm⟩
    · iframe; iframe #
    simp only [decide_eq_false (show e' ≠ W64 0 from he'), Bool.not_false]
    wp_auto
    by_cases he'2 : e' = W64 2
    · rw [decide_eq_true he'2]
      wp_auto
      iapply HΦ
      iframe
      iapply os.peOk_null
    rw [decide_eq_false he'2]
    try wp_auto
    by_cases he'20 : e' = W64 20
    · rw [decide_eq_true he'20]
      try wp_auto
      wp_apply os.model.wp_pathErrorPtr_errno _ _ _ he0' as %pe Hpe
      try wp_auto
      iapply HΦ
      iframe
    rw [decide_eq_false he'20]
    try wp_auto
    wp_apply os.model.wp_pathErrorPtr_errno _ _ _ he' as %pe Hpe
    try wp_auto
    wp_apply os.model.wp_rmdirLoop_absentN p c R J N dq dqn hc qc hcN hN hn
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
      iapply os.peOk_null
    rw [decide_eq_false he42]
    try wp_auto
    by_cases hpn : pe = null
    · simp only [decide_eq_true hpn, Bool.not_true]
      try wp_auto
      wp_apply os.model.wp_pathErrorPtr_errno _ _ _ he4 as %pe' Hpe'
      iapply HΦ
      iframe
    · simp only [decide_eq_false hpn, Bool.not_false]
      try wp_auto
      iapply HΦ
      iframe

set_option hygiene false in
/-- The end of `RemoveAll` (`RemoveAll.lean`'s): the guard's `LstatDir`, the guard's fraction (half
of `qc`) back. -/
local macro "rm_finN" qc:term:max fin:tacticSeq : tactic => `(tactic| (
  try wp_auto
  wp_apply wp_osLstatDirGuardS R (child d b) t sg ($qc).half hp CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi Hg as %isDir %e5 %- Hg
  iapply HΦ
  iframe
  isplitl [Hperm Hg]
  · iapply (os.osCallPerm_halves $qc).1; iframe
  ($fin)))

theorem os.RemoveAll.wp_proofAbsentN : os.RemoveAll.specAbsentN (GF := GF) (hG := hG) := by
  intro d b j R qd N dqn h qc hb hN hn
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  icases os.osPathS_facts R d _ j b hb $$ Hp with %hpf
  obtain ⟨hd, hp⟩ := hpf
  rw [decide_eq_false (show child d b ≠ [] by simp [child])]
  wp_auto
  wp_apply os.wp_endsWithDot_child d b hb
  imod osLogLb_0 with #Hlb
  icases (os.osCallPerm_halves qc).2 $$ Hperm with ⟨Hg, Hperm⟩
  wp_apply +noauto wp_osCallBeginGuardS R qc.half 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hg Hlb as %t %sg %- Hg #Hlsg
  wp_auto
  wp_apply os.model.wp_unlinkLoop_absentN d b R j N (DFrac.own qd) dqn h qc.half hb hN hn
    $$ [Hp Hn Hperm] as %e ⟨%he0, Hp, Hn, Hperm⟩
  · iframe; iframe #
  rw [decide_eq_false (show e ≠ W64 0 from he0)]
  wp_auto
  wp_apply os.model.wp_rmdirLoop_absentN d b R j N (DFrac.own qd) dqn h qc.half hb hN hn
    $$ [Hp Hn Hperm] as %e1 ⟨%he1, Hp, Hn, Hperm⟩
  · iframe; iframe #
  rw [decide_eq_false (show e1 ≠ W64 0 from he1)]
  wp_auto
  by_cases he20 : e1 = W64 20
  all_goals first
    | (simp only [decide_eq_true he20, Bool.not_true]; wp_auto; generalize e = e2)
    | (simp only [decide_eq_false he20, Bool.not_false]; wp_auto; generalize e1 = e2)
  all_goals
    by_cases he22 : e2 = W64 2
    · rw [decide_eq_true he22]
      rm_finN qc
        simp only [fmtErrorOkOrNil]; itrivial
    rw [decide_eq_false he22]
    wp_auto
    wp_apply os.wp_splitPath_child d b hb hd
    wp_apply os.model.wp_openLoop_spine d R j (DFrac.own qd) qc.half $$ [Hp Hperm]
      as %fd %eo ⟨Hp, Hperm, Ho⟩
    · iframe; iframe #
    icases Ho with (%heo | ⟨%heo, Hfd⟩)
    · by_cases heo2 : eo = W64 2
      · rw [decide_eq_true heo2]
        rm_finN qc
          simp only [fmtErrorOkOrNil]; itrivial
      rw [decide_eq_false heo2]
      wp_auto
      simp only [decide_eq_false (show eo ≠ W64 0 from heo), Bool.not_false]
      wp_auto
      wp_apply os.wp_pathError_ok _ _ eo heo as %pe #Hok
      rm_finN qc
        iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok
    · rw [decide_eq_false (show eo ≠ W64 2 by rw [heo]; decide)]
      wp_auto
      simp only [decide_eq_true (show eo = W64 0 from heo), Bool.not_true]
      wp_auto
      wp_apply os.model.wp_removeAllFrom_absentN d b R j N (DFrac.own qd) dqn h qc.half hb hN hn
        $$ [Hp Hn Hperm] as %pe ⟨Hp, Hperm, Hpe, Hn⟩
      · iframe; iframe #
      wp_apply os.model.wp_closeFd_dir fd j _ $$ [Hfd]
      · iframe; iframe #
      by_cases hpn : pe = null
      · rw [decide_eq_true hpn]
        rm_finN qc
          simp only [fmtErrorOkOrNil]; itrivial
      rw [decide_eq_false hpn]
      wp_auto
      wp_apply os.model.wp_prefixPath pe d $$ Hpe as Hpe
      imod os.peOk_fmt pe hpn $$ Hpe with #Hok
      rm_finN qc
        iexact Hok

end proof

end EtcdGrove
end Perennial
