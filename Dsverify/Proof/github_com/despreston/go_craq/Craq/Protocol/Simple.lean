/-
The protocol's simple ghost laws: `cvLb`, `tailTok`, `valsElem`, roles, node logs, `covers`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Protocol.Pure

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.despreston.go_craq

section simple
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem cv_halves (γ : GName) (L : CLog) :
    monoListAuthOwn (GF := GF) γ 1 L ⊣⊢
      monoListAuthOwn γ (1 : Qp).half L ∗ monoListAuthOwn γ (1 : Qp).half L := by
  have := (monoListAuthOwn_fractional (GF := GF) γ L).fractional (1 : Qp).half (1 : Qp).half
  rwa [Qp.half_add_half] at this

/-- Two halves of a commit log agree and grow together. -/
theorem cv_halves_update (γ : GName) {l1 l2 l' : CLog} (h : l1 <+: l') :
    ⊢ monoListAuthOwn (GF := GF) γ (1 : Qp).half l1 -∗ monoListAuthOwn γ (1 : Qp).half l2 ==∗
      ⌜l1 = l2⌝ ∗ monoListAuthOwn γ (1 : Qp).half l' ∗ monoListAuthOwn γ (1 : Qp).half l' := by
  iintro H1 H2
  ihave %Hag := monoListAuthOwn_agree _ _ _ _ _ $$ H1 H2
  obtain ⟨-, rfl⟩ := Hag
  ihave Hf := (cv_halves γ l1).2 $$ [$H1 $H2]
  imod monoListAuthOwn_update l' h $$ Hf with ⟨Hf, -⟩
  icases (cv_halves γ l').1 $$ Hf with ⟨H1, H2⟩
  imodintro
  iframe
  ipureintro; rfl

/-- A `cvLb` against any authority of the commit log. -/
theorem cvLb_auth (γ : CraqNames) (q : Qp) (L : CLog) (k : GoString) (v : w64) :
    ⊢ monoListAuthOwn (GF := GF) γ.cv q L -∗ cvLb γ k v -∗ ⌜uint.Z v ≤ uint.Z (cvOf L k)⌝ := by
  iintro HL Hlb
  unfold cvLb
  icases Hlb with (%Hv | ⟨%L0, Hlb, %Hle⟩)
  · subst Hv
    ipureintro
    word
  · ihave %Hp := mono_list_auth_lb_valid _ _ _ _ $$ HL Hlb
    ipureintro
    exact Int.le_trans Hle (cvOf_prefix Hp.2 k)

theorem tailTok_cvLb.holds : tailTok_cvLb.spec (GF := GF) (G := G) := by
  intro γ L k v
  iintro ⟨HL, Hlb⟩
  unfold tailTok
  iapply cvLb_auth $$ HL Hlb

theorem tailTok_lb.holds : tailTok_lb.spec (GF := GF) (G := G) := by
  intro γ L k
  iintro HL
  unfold tailTok
  ihave #Hlb := monoListLbOwn_get _ _ _ $$ HL
  iframe HL
  unfold cvLb
  iright
  iexists L
  iframe Hlb
  ipureintro; exact Int.le_refl _

theorem cvLb_zero.holds : cvLb_zero.spec (GF := GF) (G := G) := by
  intro γ k
  unfold cvLb
  ileft
  ipureintro; rfl

theorem cvLb_mono.holds : cvLb_mono.spec (GF := GF) (G := G) := by
  intro γ k v v' h
  unfold cvLb
  iintro (%Hv | ⟨%L0, Hlb, %Hle⟩)
  · ileft
    ipureintro
    subst Hv
    word
  · iright
    iexists L0
    iframe Hlb
    ipureintro; exact Int.le_trans h Hle

theorem valsElem_agree.holds : valsElem_agree.spec (GF := GF) (G := G) := by
  intro γ v k x k' x'
  unfold valsElem
  iintro ⟨⟨-, %p, %c, H1⟩, ⟨-, %p', %c', H2⟩⟩
  ihave %Hag := ghostMapElem_agree _ _ _ _ _ _ $$ H1 H2
  ipureintro
  simp only [Prod.mk.injEq] at Hag
  exact ⟨Hag.1, Hag.2.1⟩

theorem covers_nil.holds : covers_nil.spec (GF := GF) (G := G) := by
  intro γ a
  imod monoListLbOwn_nil (GF := GF) (A := GoString × w64) (γ.nlog a) with Hlb
  imodintro
  unfold covers
  iexists []
  iframe Hlb
  ipureintro; intro k; exact Int.le_refl _

theorem roleHalf_agree.holds : roleHalf_agree.spec (GF := GF) (G := G) := by
  intro γ a r r'
  unfold roleHalf
  iintro ⟨H1, H2⟩
  iapply ghostVar_agree $$ H1 H2

theorem roleHalf_update.holds : roleHalf_update.spec (GF := GF) (G := G) := by
  intro γ a r r' r''
  unfold roleHalf
  iintro ⟨H1, H2⟩
  iapply ghostVar_update_halves $$ H1 H2

theorem nlog_covers.holds : nlog_covers.spec (GF := GF) (G := G) := by
  intro γ a Ln
  unfold nlogAuth covers
  iintro HL
  ihave #Hlb := monoListLbOwn_get _ _ _ $$ HL
  iframe HL
  iexists Ln
  iframe Hlb
  ipureintro; intro k; exact Int.le_refl _

theorem nlog_covers_le.holds : nlog_covers_le.spec (GF := GF) (G := G) := by
  intro γ a Ln L
  unfold nlogAuth covers
  iintro ⟨HL, ⟨%L', Hlb, %Hle⟩⟩
  ihave %Hp := mono_list_auth_lb_valid _ _ _ _ $$ HL Hlb
  ipureintro
  intro k
  exact Int.le_trans (Hle k) (cvOf_prefix Hp.2 k)

theorem nlog_append.holds : nlog_append.spec (GF := GF) (G := G) := by
  intro γ a Ln k v
  unfold nlogAuth
  iintro HL
  imod monoListAuthOwn_update_app [(k, v)] $$ HL with ⟨HL, -⟩
  imodintro
  iexact HL

theorem covers_mono.holds : covers_mono.spec (GF := GF) (G := G) := by
  intro γ a L L' h
  unfold covers
  iintro ⟨%L0, Hlb, %Hle⟩
  iexists L0
  iframe Hlb
  ipureintro
  intro k
  exact Int.le_trans (h k) (Hle k)

end simple

end github_com.despreston.go_craq

end Perennial
