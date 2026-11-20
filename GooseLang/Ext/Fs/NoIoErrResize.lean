/-
The second step of a resize (`ftruncate`'s and `fallocate`'s growth, `FtruncateFinish`/`FallocFinish`)
under the premise **no I/O error on chosen files** (`NoIoErr S`, every inode covered): errno 0 when its
target is at most `maxBytes` (`ftFinish_noErr`, `fallocFinish_noErr`), read off the state through the
resize's token (`rsTok_inflight`, as `pwTok_inflight` for a `pwrite`). wal-fsfix2 (2026-11-20).
Untrusted.
-/
module

public import GooseLang.Ext.Fs.NoIoErrSpecs
public import GooseLang.Ext.Fs.Truncate

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section step
variable [GooseExts] [GoGlobalContext] [S : ExtSemantics fsExt] [FsSemOk]

/-- Every step of `ftruncate`'s end on the token `t` of the change `c0` (a resize to `sz`, at most
`maxBytes`) returns errno 0 when every inode is covered. -/
theorem ftFinish_noErr {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (t : Nat) (c0 : OsChange) (sz : Nat) :
    ∀ h st g e' h' st' g', (st.proc.inflight !! t = some c0 ∧ c0.kind = .truncate sz ∧
        c0.target ≤ maxBytes) →
      S.step "FtruncateFinish" (osTokV t) h st g e' h' st' g' →
      ∃ r, e' = Val r ∧ r = #(0 : w64) := by
  intro h st g e' h' st' g' ⟨hc0, hk0, htg⟩ hs
  have hf := fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)
  obtain ⟨hst, -, -⟩ := hf
  simp only [IsFsStep] at hst
  obtain ⟨t', c, sz', f, hv, hc, hk, hfl, -⟩ := hst
  have htt : t = t' := by injection hv with hv; exact extVal_inj hv
  subst htt
  rw [hc0] at hc; cases hc
  have hz := noIoErr_step (Sio := Sio) hs (by simp only [IoCovers]; exact ⟨t, c0, rfl, hc0, hS _ _⟩)
    ⟨Val (#(0 : w64)), (st.doneInflight t).setFile c0.ino (f.land c0 c0.hi c0.target),
      by simp only [IsFsStep]; exact ⟨t, c0, sz', f, rfl, hc0, hk, hfl, .inl ⟨htg, by trivial, by trivial⟩⟩,
      (rfl : Val (#(0 : w64)) = Val (#(0 : w64)))⟩
  exact ⟨_, (hz : e' = Val (#(0 : w64))), rfl⟩

/-- Every step of `fallocate`'s end on the token `t` of the change `c0` (a growth to `sz`, at most
`maxBytes`) returns errno 0 when every inode is covered. -/
theorem fallocFinish_noErr {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (t : Nat) (c0 : OsChange) (sz : Nat) :
    ∀ h st g e' h' st' g', (st.proc.inflight !! t = some c0 ∧ c0.kind = .falloc sz ∧
        c0.target ≤ maxBytes) →
      S.step "FallocFinish" (osTokV t) h st g e' h' st' g' →
      ∃ r, e' = Val r ∧ r = #(0 : w64) := by
  intro h st g e' h' st' g' ⟨hc0, hk0, htg⟩ hs
  have hf := fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)
  obtain ⟨hst, -, -⟩ := hf
  simp only [IsFsStep] at hst
  obtain ⟨t', c, sz', f, hv, hc, hk, hfl, -⟩ := hst
  have htt : t = t' := by injection hv with hv; exact extVal_inj hv
  subst htt
  rw [hc0] at hc; cases hc
  have hz := noIoErr_step (Sio := Sio) hs (by simp only [IoCovers]; exact ⟨t, c0, rfl, hc0, hS _ _⟩)
    ⟨Val (#(0 : w64)), (st.doneInflight t).setFile c0.ino (f.land c0 c0.hi c0.target),
      by simp only [IsFsStep]; exact ⟨t, c0, sz', f, rfl, hc0, hk, hfl, .inl ⟨htg, by trivial, by trivial⟩⟩,
      (rfl : Val (#(0 : w64)) = Val (#(0 : w64)))⟩
  exact ⟨_, (hz : e' = Val (#(0 : w64))), rfl⟩

end step

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- A resize's token says what is in flight under it: a change of its kind and target. -/
theorem rsTok_inflight (tr : Bool) (t : Nat) (p : Ino) (tg : Nat) (m : OsMeta) (xs : List ByteG)
    (n : Nat) (st : OsState) :
    iprop(rsTok (L := L) tr t p tg m xs n ∗ ExtInterp.localCtx (E := fsExt) (extLocalGS fsExt) st)
      ⊢ ⌜∃ c, st.proc.inflight !! t = some c ∧ c.kind = rsKind tr tg ∧ c.target = tg⌝ := by
  iintro ⟨Ht, Hc⟩
  icases (os_local_ctx_eq st).mp $$ Hc with Hc
  unfold rsTok osTok osCtx osCtxF
  icases Ht with ⟨Ht, -⟩
  icases Hc with ⟨⟨%Γb, %Γm, %Γf, %Γt, %Hwc, -, -, -, HAt, -⟩, -⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAt Ht with %Hti
  ipureintro
  obtain ⟨c, hct⟩ : ∃ c, st.proc.inflight !! t = some c := by
    have := Hwc.2.toks t; rw [Hti] at this; exact Option.isSome_iff_exists.1 this.symm
  obtain ⟨-, hckind, -, -, htarget, -⟩ := Hwc.2.tok_is t _ c Hti hct
  refine ⟨c, hct, hckind, ?_⟩
  rw [htarget]; unfold TokInfo.target rsKind; cases tr <;> rfl

end specs

end Fs
end Perennial
