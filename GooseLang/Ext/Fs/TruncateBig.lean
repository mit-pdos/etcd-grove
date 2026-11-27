/-
The second step of an `ftruncate` past `maxBytes` (Lean-first, no Rocq counterpart).

The extension's `FtruncateFinish` (`Impl.lean`) lands the resize only for a target at most
`maxBytes` (both its landing outcomes require `c.target ≤ maxBytes`); past it the step fails with a
nonzero errno and the state as the first step left it (`EFBIG`, `data_maxbytes.go`), whatever the
file system's errors (`FsNoErr` does not exclude it). `wp_osFtruncateFinish` does not say so (its
landed arms are there for any target); `wp_osFtruncateFinishBig` is its case past `maxBytes`: an
error, and the file as the first step announced it (`rsUndone`).
-/
module

public import GooseLang.Ext.Fs.Truncate

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable

/-- **The second step of an `ftruncate` to a target past `maxBytes`**: it fails (nonzero errno),
the file as its first step left it. -/
theorem wp_osFtruncateFinishBig (t : Nat) (p : Ino) (tg : Nat) (m : OsMeta) (xs : List ByteG)
    (n : Nat) (hbig : maxBytes < tg) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ rsTok (L := L) true t p tg m xs n -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ rsUndone (L := L) true p tg m xs n -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "FtruncateFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  iintro #Hinv Ht HΦ
  iapply wp_os_step "FtruncateFinish" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold rsTok osTok
  icases Ht with ⟨Ht, %hxl⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAt Ht with %Hti
  obtain ⟨c, f, hF⟩ := rsFacts_of hcoh Hti hxl
  have hcp := hF.hcino
  subst hcp
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
    intro l hm
    obtain ⟨x, hx⟩ := cellView_isSome hwf hm
    obtain ⟨m0, hm0⟩ := Hag l x hx
    rw [hm0]; rfl
  have hnot : ¬ c.target ≤ maxBytes := by rw [hF.hctg]; omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, renderHeap (st.doneInflight t) h, _,
      ⟨t, c, tg, f, rfl, hF.hct, hF.hckind, hF.hf, .inr ⟨27, by decide, rfl, .inl rfl⟩⟩,
      mapsFresh_same rfl, heapRendered_render (osWf_done hwf) rfl Hh⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨t', c', tg', f', hv, hinfl, hkind', hf', hres⟩ := Hst
  have htt : t = t' := by injection hv with hv; exact extVal_inj hv
  subst htt
  rw [hF.hct, Option.some.injEq] at hinfl; subst hinfl
  rw [hF.hckind] at hkind'; simp only [rsKind, if_true] at hkind'; injection hkind' with ho; subst ho
  rw [hF.hf, Option.some.injEq] at hf'; subst hf'
  rcases hres with ⟨htm, -, -⟩ | ⟨e, he, rfl, rfl | ⟨htm, -⟩⟩
  · exact absurd htm hnot
  · imod resize_undone_worldK false hwf hcoh hF Hr Hfr $$ HAb HAm HAf HAt Htok Hcells Hσ Ht
      with ⟨⟨%Γb', %Γm', %Γf', %Γt', Hw⟩, Hd⟩
    imodintro
    iexists Γb', Γm', Γf', Γt'
    isplitl [Hw]
    · iapply (osWorld_unfold (L := L)).1 $$ Hw
    iapply wp_value'
    iapply HΦ $$ %e %he
    rw [← rsUndoneK_false]; iexact Hd
  · exact absurd htm hnot

end specs

end Fs
end Perennial
