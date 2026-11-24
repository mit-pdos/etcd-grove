/-
The proof of `Spec/os/RemoveAll.lean` (`notes/wal-fsext-i2-design.md`, "Implementation log,
`os.RemoveAll`"). The model holds a guard call (`wp_osCallBeginGuardS`, a fraction `g` of the call
permission) from its start to its `LstatDir` (`wp_osLstatDirGuardS`); every inner call takes the
rest. Lean-first; untrusted.
-/
module

public import Proof.os.RemoveAllTop

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
/-- The end of `RemoveAll`: the guard's `LstatDir`, the guard's fraction (half of `qc`) back. -/
local macro "rm_fin" qc:term:max fin:tacticSeq : tactic => `(tactic| (
  try wp_auto
  -- PORT: which stub? (LstatDirGuardS)
  wp_apply wp_osLstatDirGuardS R (child d b) t sg ($qc).half hp CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi Hg as %isDir %e5 %- Hg
  icases osCallPerm_unchild R d b _ _ _ $$ Hp Hg with ⟨Hp, Hg⟩
  iapply HΦ
  iframe
  isplitl [Hperm Hg]
  · iapply (os.osCallPerm_halves _ $qc).1; iframe
  ($fin)))

theorem os.RemoveAll.wp_proofAbsentS : os.RemoveAll.specAbsentS (GF := GF) (hG := hG) := by
  intro d b j R qd dqn h qc hb hn
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  icases os.osPathS_facts R d _ j b hb $$ Hp with %hpf
  obtain ⟨hd, hp⟩ := hpf
  rw [decide_eq_false (show child d b ≠ [] by simp [child])]
  try wp_auto
  wp_apply os.wp_endsWithDot_child d b hb
  imod osLogLb_0 with #Hlb
  icases (os.osCallPerm_halves _ qc).2 $$ Hperm with ⟨Hg, Hperm⟩
  icases osCallPerm_child R d b _ _ _ $$ Hp Hg with ⟨Hp, Hg⟩
  wp_apply +noauto wp_osCallBeginGuardS R _ qc.half 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hg Hlb as %t %sg %- Hg #Hlsg
  try wp_auto
  have hnd : ∀ J, h.cur !! b ≠ some (.dir J) := fun J h' => by rw [hn] at h'; cases h'
  wp_apply os.model.wp_unlinkLoop_leaf d b R j (DFrac.own qd) dqn h qc.half hb hnd (.inr hn)
    $$ [Hp Hn Hperm] as %e ⟨Hp, Hperm, %h', Hn, %hlow⟩
  · iframe; iframe #
  obtain ⟨hlo, -⟩ := hlow
  obtain rfl := hlo.2 hn
  by_cases he0 : e = W64 0
  · rw [decide_eq_true he0]
    rm_fin qc
      simp only [fmtErrorOkOrNil]; itrivial
  rw [decide_eq_false he0]
  try wp_auto
  wp_apply os.model.wp_rmdirLoop_none d b R j (DFrac.own qd) dqn _ qc.half hb hnd
    $$ [Hp Hn Hperm] as %e1 ⟨%he1, Hp, Hn, Hperm⟩
  · iframe; iframe #
  rw [decide_eq_false (show e1 ≠ W64 0 from he1)]
  try wp_auto
  by_cases he20 : e1 = W64 20
  all_goals first
    | (simp only [decide_eq_true he20, Bool.not_true]; wp_auto; generalize e = e2)
    | (simp only [decide_eq_false he20, Bool.not_false]; wp_auto; generalize e1 = e2)
  all_goals
    by_cases he22 : e2 = W64 2
    · rw [decide_eq_true he22]
      rm_fin qc
        simp only [fmtErrorOkOrNil]; itrivial
    rw [decide_eq_false he22]
    try wp_auto
    wp_apply os.wp_splitPath_child d b hb hd
    wp_apply os.model.wp_openLoop_spine d R j (DFrac.own qd) qc.half $$ [Hp Hperm]
      as %fd %eo ⟨Hp, Hperm, Ho⟩
    · iframe; iframe #
    icases Ho with (%heo | ⟨%heo, Hfd⟩)
    · by_cases heo2 : eo = W64 2
      · rw [decide_eq_true heo2]
        rm_fin qc
          simp only [fmtErrorOkOrNil]; itrivial
      rw [decide_eq_false heo2]
      try wp_auto
      simp only [decide_eq_false (show eo ≠ W64 0 from heo), Bool.not_false]
      try wp_auto
      wp_apply os.wp_pathError_ok _ _ eo heo as %pe #Hok
      rm_fin qc
        iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok
    · rw [decide_eq_false (show eo ≠ W64 2 by rw [heo]; decide)]
      try wp_auto
      simp only [decide_eq_true (show eo = W64 0 from heo), Bool.not_true]
      try wp_auto
      wp_apply os.model.wp_removeAllFrom_leaf d b R j (DFrac.own qd) dqn h' qc.half hb hnd (.inr hn)
        $$ [Hp Hn Hperm] as %pe ⟨Hp, Hperm, Hpe, %h'', Hn, %hlo'w⟩
      · iframe; iframe #
      obtain ⟨hlo', -⟩ := hlo'w
      obtain rfl := hlo'.2 hn
      wp_apply os.model.wp_closeFd_dir fd j _ $$ [Hfd]
      · iframe; iframe #
      by_cases hpn : pe = null
      · rw [decide_eq_true hpn]
        rm_fin qc
          simp only [fmtErrorOkOrNil]; itrivial
      rw [decide_eq_false hpn]
      try wp_auto
      wp_apply os.model.wp_prefixPath pe d $$ Hpe as Hpe
      imod os.peOk_fmt pe hpn $$ Hpe with #Hok
      rm_fin qc
        iexact Hok

theorem os.RemoveAll.wp_proofDirS : os.RemoveAll.specDirS (GF := GF) (hG := hG) := by
  intro d b j J R qd h hJ hb hbJ hfo
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, HJ, Hperm⟩
  icases os.osPathS_facts R d _ j b hb $$ Hp with %hpf
  obtain ⟨hd, hp⟩ := hpf
  ihave Hst : rmAllOut j b J h hJ $$ [Hn HJ]
  · iapply os.rmPresent_out; unfold os.rmPresent; iexists hJ; iframe; ipureintro
    exact EntsSub.refl _
  rw [decide_eq_false (show child d b ≠ [] by simp [child])]
  try wp_auto
  wp_apply os.wp_endsWithDot_child d b hb
  imod osLogLb_0 with #Hlb
  icases (os.osCallPerm_halves _ 1).2 $$ Hperm with ⟨Hg, Hperm⟩
  icases osCallPerm_child R d b _ _ _ $$ Hp Hg with ⟨Hp, Hg⟩
  wp_apply +noauto wp_osCallBeginGuardS R _ (1 : Qp).half 0 CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi Hg Hlb as %t %sg %- Hg #Hlsg
  try wp_auto
  have hqg : (1 : Qp).half + (1 : Qp).half = 1 := Qp.half_add_half 1
  wp_apply os.model.wp_unlinkLoop_dirSt d b j J R (DFrac.own qd) h hJ (1 : Qp).half hb hbJ
    $$ [Hp Hst Hperm] as %e ⟨%he0, Hp, Hst, Hperm⟩
  · iframe; iframe #
  rw [decide_eq_false (show e ≠ W64 0 from he0)]
  try wp_auto
  wp_apply os.model.wp_rmdirLoop_dirSt d b j J R qd h hJ (1 : Qp).half (1 : Qp).half t sg (child d b) rfl
    hb hbJ
    hqg $$ [Hp Hst Hperm Hg] as %e1 ⟨Hp, Hst, Hperm, Hg⟩
  · iframe; iframe #
  by_cases he10 : e1 = W64 0
  · rw [decide_eq_true he10]
    rm_fin (1 : Qp)
      simp only [fmtErrorOkOrNil]; itrivial
  rw [decide_eq_false he10]
  try wp_auto
  by_cases he20 : e1 = W64 20
  all_goals first
    | (simp only [decide_eq_true he20, Bool.not_true]; wp_auto; generalize e = e2)
    | (simp only [decide_eq_false he20, Bool.not_false]; wp_auto; generalize e1 = e2)
  all_goals
    by_cases he22 : e2 = W64 2
    · rw [decide_eq_true he22]
      rm_fin (1 : Qp)
        simp only [fmtErrorOkOrNil]; itrivial
    rw [decide_eq_false he22]
    try wp_auto
    wp_apply os.wp_splitPath_child d b hb hd
    wp_apply os.model.wp_openLoop_spine d R j (DFrac.own qd) (1 : Qp).half $$ [Hp Hperm]
      as %fd %eo ⟨Hp, Hperm, Ho⟩
    · iframe; iframe #
    icases Ho with (%heo | ⟨%heo, Hfd⟩)
    · by_cases heo2 : eo = W64 2
      · rw [decide_eq_true heo2]
        rm_fin (1 : Qp)
          simp only [fmtErrorOkOrNil]; itrivial
      rw [decide_eq_false heo2]
      try wp_auto
      simp only [decide_eq_false (show eo ≠ W64 0 from heo), Bool.not_false]
      try wp_auto
      wp_apply os.wp_pathError_ok _ _ eo heo as %pe #Hok
      rm_fin (1 : Qp)
        iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok
    · rw [decide_eq_false (show eo ≠ W64 2 by rw [heo]; decide)]
      try wp_auto
      simp only [decide_eq_true (show eo = W64 0 from heo), Bool.not_true]
      try wp_auto
      wp_apply os.model.wp_removeAllFrom_dir d b j J R qd h hJ (1 : Qp).half (1 : Qp).half t sg hb
        hbJ hfo hqg $$ [Hp Hst Hperm Hg] as %pe ⟨Hp, Hst, Hperm, Hg, Hpe⟩
      · iframe; iframe #
      wp_apply os.model.wp_closeFd_dir fd j _ $$ [Hfd]
      · iframe; iframe #
      by_cases hpn : pe = null
      · rw [decide_eq_true hpn]
        rm_fin (1 : Qp)
          simp only [fmtErrorOkOrNil]; itrivial
      rw [decide_eq_false hpn]
      try wp_auto
      wp_apply os.model.wp_prefixPath pe d $$ Hpe as Hpe
      imod os.peOk_fmt pe hpn $$ Hpe with #Hok
      rm_fin (1 : Qp)
        iexact Hok

end proof

end EtcdGrove
end Perennial
