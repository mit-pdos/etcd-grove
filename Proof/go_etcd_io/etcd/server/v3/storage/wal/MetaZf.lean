/- Lean-first (no Rocq counterpart).

# The zeros known past an `OsMeta` start at or past its size (`MetaOk.zf`)

`Fs.wp_osMeta_zfGe` (moved here from `FdatasyncPend.lean`, unit `locks`, session 8, so that `WAL.cut` uses it
too): before any step of a non-value expression, the state's `MetaOk` gives it of any `OsMeta` held. The
tail's sync steps need it (`hzf`), and `cut`'s rename of the old tail into the segments before the last
(`WalFullOk`'s `SegsZf`).
-/
module

public import GooseLang.Ext.Fs.Specs
public import GooseLang.Ext.Fs.World

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial

namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **The zeros known past an `OsMeta` start at or past its size** (`MetaOk.zf` and `MetaOk.size`; as
`wp_osMeta_size`): before any step of a non-value `e`. -/
theorem wp_osMeta_zfGe (e : Expr) (Φ : val → IProp GF) (h : toVal e = none) (i : Ino) (dq : DFrac)
    (m : OsMeta) :
    ⊢ osMeta (L := L) i dq m -∗
      (⌜∀ z, m.zf = some z → m.size ≤ z⌝ -∗ osMeta (L := L) i dq m -∗ WP e @ s; E {{ Φ }}) -∗
      WP e @ s; E {{ Φ }} := by
  iintro Hm Hk
  iapply wp_ext_acc (X := fsExt) e Φ h
  iintro %σ %g Hl Hg
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx osCtxF osMeta
  icases Hl with ⟨⟨%Γb, %Γm, %Γf, %Γt, %Hwc, HAb, HAm, HAf, HAt, Htok, Hv⟩, Hns, Hof⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  obtain ⟨f, hf, hmo⟩ := coh_meta Hwc.2 Hml
  have hz : ∀ z, m.zf = some z → m.size ≤ z := fun z hz => by
    rw [hmo.size]; exact (hmo.zf z hz).1
  ihave Hwp := Hk $$ %hz Hm
  imodintro
  iframe Hg Hwp
  iapply (os_local_ctx_eq σ).mpr
  unfold osCtx osCtxF
  iframe Hns Hof
  iexists Γb, Γm, Γf, Γt
  iframe
  ipureintro; exact Hwc

end specs

end Fs

end Perennial

end
