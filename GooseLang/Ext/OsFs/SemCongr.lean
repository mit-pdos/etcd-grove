/-
The WP depends on the semantics of the extensions only through their steps: two `GooseSemantics`
whose extension steps agree (`extStep`) give the same language (`goose_ectxi_lang`) and so the
same WP (`wp_sem_congr`). A crash relation is no part of the WP.

`CrashP1.lean` uses it to run a proof made in the terms of the Linux file extension's semantics
(`osFs_semantics`, for which the specs are proved) in a program closed with the same step and a
stronger crash relation. Generic; it could live in Perennial (`Lifting.lean`).
-/
module

public import Perennial.GooseLang.Lifting

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section congr
variable [GooseExts] [GoGlobalContext]

theorem baseStep_sem_mono {Sa Sb : GooseSemantics}
    (hext : ∀ ext op v σg e' σg', @extStep _ Sa _ ext op v σg e' σg' → @extStep _ Sb _ ext op v σg e' σg')
    {e σ κ e' σ' efs} (h : @BaseStep _ Sa _ e σ κ e' σ' efs) : @BaseStep _ Sb _ e σ κ e' σ' efs := by
  cases h
  case ExternalOpS h => exact .ExternalOpS _ _ _ _ _ _ (hext _ _ _ _ _ _ h)
  all_goals (constructor <;> assumption)

theorem headStep_sem_mono {Sa Sb : GooseSemantics}
    (hext : ∀ ext op v σg e' σg', @extStep _ Sa _ ext op v σg e' σg' → @extStep _ Sb _ ext op v σg e' σg')
    {e σ κ e' σ' efs} (h : @HeadStep _ Sa _ e σ κ e' σ' efs) : @HeadStep _ Sb _ e σ κ e' σ' efs := by
  cases h with
  | unwind hu => exact .unwind hu
  | base hu hb => exact .base hu (baseStep_sem_mono hext hb)

theorem boundedBaseStep_sem_mono {Sa Sb : GooseSemantics}
    (hext : ∀ ext op v σg e' σg', @extStep _ Sa _ ext op v σg e' σg' → @extStep _ Sb _ ext op v σg e' σg')
    {e σ κ e' σ' efs} (h : @BoundedBaseStep _ Sa _ e σ κ e' σ' efs) :
    @BoundedBaseStep _ Sb _ e σ κ e' σ' efs := by
  cases h with
  | step hk h => exact .step hk (headStep_sem_mono hext h)
  | tick hk h => exact .tick hk (headStep_sem_mono hext h)
  | stutter hk h => exact .stutter hk (headStep_sem_mono hext h)
  | fork h => exact .fork (headStep_sem_mono hext h)
  | forkStutter => exact .forkStutter
  | exit h => exact .exit (headStep_sem_mono hext h)

/-- Two semantics with the same extension steps give the same language. -/
theorem goose_ectxi_lang_congr {Sa Sb : GooseSemantics}
    (hext : ∀ ext op v σg e' σg', @extStep _ Sa _ ext op v σg e' σg' ↔ @extStep _ Sb _ ext op v σg e' σg') :
    @goose_ectxi_lang _ Sa _ = @goose_ectxi_lang _ Sb _ := by
  have hb : (@BoundedBaseStep _ Sa _) = (@BoundedBaseStep _ Sb _) := by
    funext e σ κ e' σ' efs
    exact propext ⟨boundedBaseStep_sem_mono (fun _ _ _ _ _ _ => (hext _ _ _ _ _ _).1),
      boundedBaseStep_sem_mono (fun _ _ _ _ _ _ => (hext _ _ _ _ _ _).2)⟩
  unfold goose_ectxi_lang
  congr 1
  rw [hb]

end congr

section wp
variable [GooseExts] [GooseInterp] [GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors}

/-- The language of an `EctxItemLanguage` instance, as the WP takes it. -/
abbrev langOf (Λ : EctxItemLanguage Expr EctxItem BcfgState Observation val) :=
  @EctxLanguage.instLanguage _ _ _ _ (@EctxItemLanguage.Ectx _ _ _ _ EctxItem Λ)
    (@EctxItemLanguage.instEctxLanguage _ _ _ _ EctxItem Λ)

/-- `goose_irisGS` over any language instance `Λ` (it uses its semantics only through `Λ`). -/
@[reducible] def gooseIrisGSOf [G : GooseGlobalGS hlc GF] [GooseLocalGS GF]
    (Λ : EctxItemLanguage Expr EctxItem BcfgState Observation val) :
    @IrisGS_gen hlc Expr val BcfgState Observation
      (@EctxLanguage.instLanguage _ _ _ _ (@EctxItemLanguage.Ectx _ _ _ _ EctxItem Λ)
        (@EctxItemLanguage.instEctxLanguage _ _ _ _ EctxItem Λ)) GF where
  toStateInterp := goose_stateInterp
  invGS := G.gooseInvGS
  numLatersPerStep _ := 0
  forkPost v := iprop(⌜v.isPanic = false⌝)
  stateInterp_mono σ ns obs nt := by
    let := G.gooseInvGS
    iintro $

/-- **The WP depends on the semantics only through the extensions' steps.** -/
theorem wp_sem_congr {Sa Sb : GooseSemantics} [GooseGlobalGS hlc GF] [GooseLocalGS GF]
    (hext : ∀ ext op v σg e' σg', @extStep _ Sa _ ext op v σg e' σg' ↔ @extStep _ Sb _ ext op v σg e' σg')
    (s : Stuckness) (E : CoPset) (e : Expr) (Φ : val → IProp GF) :
    @Wp.wp (IProp GF) Expr val Stuckness
        (@wp.def hlc Expr BcfgState Observation val (langOf (@goose_ectxi_lang _ Sa _)) GF
          (@goose_irisGS _ _ hlc GF Sa _ _ _)) s E e Φ =
      @Wp.wp (IProp GF) Expr val Stuckness
        (@wp.def hlc Expr BcfgState Observation val (langOf (@goose_ectxi_lang _ Sb _)) GF
          (@goose_irisGS _ _ hlc GF Sb _ _ _)) s E e Φ := by
  show @Wp.wp (IProp GF) Expr val Stuckness
      (@wp.def hlc Expr BcfgState Observation val (langOf (@goose_ectxi_lang _ Sa _)) GF
        (gooseIrisGSOf (@goose_ectxi_lang _ Sa _))) s E e Φ =
    @Wp.wp (IProp GF) Expr val Stuckness
      (@wp.def hlc Expr BcfgState Observation val (langOf (@goose_ectxi_lang _ Sb _)) GF
        (gooseIrisGSOf (@goose_ectxi_lang _ Sb _))) s E e Φ
  rw [goose_ectxi_lang_congr hext]

end wp

end Perennial
