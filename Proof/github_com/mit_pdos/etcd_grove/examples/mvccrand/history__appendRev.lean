/- Lean-first (no Rocq counterpart). The proof of `history.appendRev`: under the write lock, the
lock's halves agree with the writer's; both slices appended (their elements persistent), the ghost
cells and the revisions' list updated with both halves. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.history__appendRev

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem statesP_snoc (ms : List GoMap) (Hs : List HRev) (m : GoMap) (r : HRev) :
    statesP (GF := GF) ms Hs ∗ m ↦$□ r.1 ⊢ statesP (ms ++ [m]) (Hs ++ [r]) := by
  iintro ⟨H, #Hm⟩
  iunfold statesP at H
  iunfold statesP
  icases H with ⟨%Hl, #H⟩
  isplitr
  · ipureintro; simp [Hl]
  rw [List.zip_append Hl]
  simp only [List.zip_cons_cons, List.zip_nil_right]
  iapply BigSepL.bigSepL_snoc.2
  iframe #

theorem changesP_snoc (cs : List GoSlice) (Hs : List HRev) (c : GoSlice) (r : HRev) :
    changesP (GF := GF) cs Hs ∗ c ↦*□ r.2 ⊢ changesP (cs ++ [c]) (Hs ++ [r]) := by
  iintro ⟨H, #Hc⟩
  iunfold changesP at H
  iunfold changesP
  icases H with ⟨%Hl, #H⟩
  isplitr
  · ipureintro; simp [Hl]
  rw [List.zip_append Hl]
  simp only [List.zip_cons_cons, List.zip_nil_right]
  iapply BigSepL.bigSepL_snoc.2
  iframe #

theorem history.appendRev.wp_proof : history.appendRev.spec (GF := GF) (hG := hG) := by
  intro h γ Hs m M c chs
  wp_start as ⟨#Hh, Hw, #Hm, #Hc⟩
  iunfold isHistory at Hh
  icases Hh with ⟨#Hg, -⟩
  iunfold histW at Hw
  icases Hw with ⟨%x, %Hx, Hgw, Hlw, Hcap1, Hcap2⟩
  wp_auto
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hg] as ⟨Hlk, HP⟩
  iunfold histR at HP
  icases HP with ⟨%x', Hs, Hcs, Hg', Hl', #He⟩
  ihave %Hag := ghostVar_agree γ.g _ _ _ _ $$ Hg' Hgw
  obtain ⟨-, rfl⟩ := Hag
  iunfold histElems at He
  icases He with ⟨%H2, #Hms, #Hcss, #Hst, #Hch⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  (try wp_auto)
  wp_apply (wp_slice_append_persistent (V := GoMap) x.1 x.2.2.1 _ [m] (DFrac.own 1))
    $$ [$Hms $Hcap1 $Hosl] as %s1 ⟨#Hs1, Hcap1, -⟩
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl2 ⟨Hosl2, -⟩
  (try wp_auto)
  wp_apply (wp_slice_append_persistent (V := GoSlice) x.2.1 x.2.2.2.1 _ [c] (DFrac.own 1))
    $$ [$Hcss $Hcap2 $Hosl2] as %s2 ⟨#Hs2, Hcap2, -⟩
  (try wp_auto)
  -- the new cells
  let x2 : HistCells := (s1, s2, x.2.2.1 ++ [m], x.2.2.2.1 ++ [c], Hs ++ [(M, chs)])
  imod ghostVar_update_halves x2 γ.g _ _ $$ Hg' Hgw with ⟨Hg', Hgw⟩
  have hone : ∀ l : List HRev, (monoListAuthOwn γ.l 1 l : IProp GF) ⊣⊢
      monoListAuthOwn γ.l (1 : Qp).half l ∗ monoListAuthOwn γ.l (1 : Qp).half l := fun l => by
    conv => lhs; rw [← Qp.half_add_half (1 : Qp)]
    exact (monoListAuthOwn_fractional (GF := GF) γ.l l).fractional _ _
  rw [Hx]
  ihave Hl := (hone Hs).2 $$ [Hl' Hlw]
  · iframe
  imod monoListAuthOwn_update_app [(M, chs)] $$ Hl with ⟨Hl, -⟩
  icases (hone _).1 $$ Hl with ⟨Hl1, Hl2⟩
  wp_apply +noauto sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hs Hcs Hg' Hl1]
  · inext
    iunfold histR
    iexists x2
    iframe
    iunfold histElems
    iframe #
    isplitr
    · ipureintro; simp only [x2, List.length_append, List.length_singleton]; rw [← Hx]; omega
    isplitr
    · iapply statesP_snoc _ _ _ (M, chs) $$ [Hst Hm]
      rw [← Hx]; iframe #
    iapply changesP_snoc _ _ _ (M, chs) $$ [Hch Hc]
    rw [← Hx]; iframe #
  wp_auto
  iapply HΦ
  iunfold histW
  iexists x2
  iframe
  ipureintro; rfl

end proof

end mvccrand
end EtcdGrove
end Perennial
