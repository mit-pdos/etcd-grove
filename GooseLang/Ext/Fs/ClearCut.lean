/-
Clearing a file's sync cut (`OsMeta.cut`), a ghost step (Lean-first, no Rocq counterpart).

A sync without the bytes (`wp_osFsyncB`, `OsMeta.bsynced`) sets the cut: the byte resources'
candidates then relate to the state's through it (`CandRel`), not equal to them. A byte-ful sync
keeps the cut as it was. The cut can be cleared again once every byte of the file is durable both
ways: the `OsMeta` whole (no change in flight) with no byte outside `[dlo, dhi)` short of durable
(`dhi ≤ dlo`: `MetaOk.dur` makes each of the state's bytes below the size its page-cache value
alone, stamped 0, as after a byte-ful sync, `OsMeta.synced`), and every byte resource of the file
held, each `durB` (its value alone, stamped 0): the two then agree exactly (`CandRel none`). Nothing
else in the ghost state reads the cut (`MetaOk` does not mention it), so the files' coherence holds
with it cleared (`osCoh_clearCut`). As a ghost step on the state interpretation, it happens before a
step of the program (`wp_osClearCut`).
-/
module

public import GooseLang.Ext.Fs.Specs

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- **The files' coherence with the cut of the file `i` cleared**: no change in flight on it, no
byte below its size short of durable (`dhi ≤ dlo`), and every byte resource of it durable. -/
theorem osCoh_clearCut {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {i : Ino}
    {m : OsMeta} (hm : Γm !! i = some m) (hnt : ∀ t ti, Γt !! t = some ti → ti.ino ≠ i)
    (hdur : m.dhi ≤ m.dlo) (hb : ∀ b x, Γb !! (i, b) = some x → x = durB x.1) :
    OsCoh st Γb (<[i := { m with cut := none }]> Γm) Γf Γt := by
  obtain ⟨f, hf, hmo⟩ := hcoh.meta_some i m hm
  refine { hcoh with
    meta_dom := fun q => ?_
    meta_some := fun q m' h => ?_
    bytes := fun q b x hx => ?_
    tok_meta := fun t ti h => ?_
    cut_le := fun q m' c h hc => ?_ }
  · rw [GMap.lookup_insert_eq_iff]
    split
    · rename_i hq; subst hq
      simp [hf]
    · exact hcoh.meta_dom q
  · rw [GMap.lookup_insert_eq_iff] at h
    split at h
    · rename_i hq; subst hq; cases h
      exact ⟨f, hf, ⟨hmo.size, hmo.lo, hmo.hi, hmo.maps, hmo.targets, hmo.dur, hmo.zf, hmo.tail,
        hmo.cz, hmo.rz, hmo.zc, hmo.ce, hmo.xs⟩⟩
    · exact hcoh.meta_some q m' h
  · obtain ⟨f1, hf1, hb1, hx1, hx2, hrel⟩ := hcoh.bytes q b x hx
    refine ⟨f1, hf1, hb1, hx1, hx2, ?_⟩
    by_cases hq : q = i
    · subst hq
      have hcut : cutOf (<[q := { m with cut := none }]> Γm) q = none := by
        simp [cutOf, GMap.lookup_insert]
      rw [hcut]
      simp only [OsState.file, hf, Option.some.injEq] at hf1
      subst hf1
      have hc := hmo.dur b hb1 (by omega)
      have hx' := hb q b x hx
      show f.cand b = x.2
      rw [hc, hx']
      simp only [durB]
      rw [hx1]
    · have hcut : cutOf (<[i := { m with cut := none }]> Γm) q = cutOf Γm q := by
        simp [cutOf, GMap.lookup_insert_ne _ _ (Ne.symm hq)]
      rw [hcut]; exact hrel
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm (hnt t ti h))]
    exact hcoh.tok_meta t ti h
  · rw [GMap.lookup_insert_eq_iff] at h
    split at h
    · cases h; simp at hc
    · exact hcoh.cut_le q m' c h hc

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **Clearing the cut of the file `i`**, before a step of a non-value `e`: with its whole `OsMeta`
`m`, none of its bytes below the size short of durable (`m.dhi ≤ m.dlo`, as after a byte-ful sync,
`OsMeta.synced`), and all of its bytes (`xs`, from 0 to the size), each durable (`durB`), the
`OsMeta` becomes `m` with no cut; the bytes come back as they were. -/
theorem wp_osClearCut (e : Expr) (Φ : val → IProp GF) (h : toVal e = none) (i : Ino) (m : OsMeta)
    (xs : List ByteG) (hl : xs.length = m.size) (hd : ∀ y ∈ xs, y = durB y.1)
    (hdur : m.dhi ≤ m.dlo) :
    osMeta (L := L) i (DFrac.own 1) m ∗ osBytes (L := L) i 0 (DFrac.own 1) xs ∗
      (osMeta (L := L) i (DFrac.own 1) { m with cut := none } -∗
        osBytes (L := L) i 0 (DFrac.own 1) xs -∗ WP e @ s; E {{ Φ }}) ⊢
      WP e @ s; E {{ Φ }} := by
  iintro ⟨Hm, Hb, Hk⟩
  iapply wp_ext_acc (X := fsExt) e Φ h
  iintro %σ %g Hl Hg
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx osCtxF
  icases Hl with ⟨⟨%Γb, %Γm, %Γf, %Γt, %Hwc, HAb, HAm, HAf, HAt, Htok, Hv⟩, Hns, Hof⟩
  unfold osMeta at Hm
  unfold osBytes at Hb
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_whole _ $$ Htok Hm with %hnt
  icases bytesG_lookup _ i 0 _ xs Γb $$ HAb Hb with %hbs
  have hb : ∀ b x, Γb !! (i, b) = some x → x = durB x.1 := by
    intro b x hx
    obtain ⟨f1, hf1, hb1, -⟩ := Hwc.2.bytes i b x hx
    obtain ⟨f, hf, hmo⟩ := Hwc.2.meta_some i m Hml
    simp only [OsState.file, hf, Option.some.injEq] at hf1; subst hf1
    have hbx : b < xs.length := by rw [hl, hmo.size]; exact hb1
    have h1 := hbs b hbx
    rw [Nat.zero_add, hx, Option.some.injEq] at h1
    subst h1
    exact hd _ (List.getElem_mem hbx)
  imod gAuth_update _ _ Γm i m { m with cut := none } $$ HAm Hm with ⟨HAm, Hm⟩
  ihave Hwp := Hk $$ [Hm] [Hb]
  · unfold osMeta; iexact Hm
  · unfold osBytes; iexact Hb
  imodintro
  iframe Hg Hwp
  iapply (os_local_ctx_eq σ).mpr
  unfold osCtx osCtxF
  iframe Hns Hof
  iexists Γb, _, Γf, Γt
  iframe
  ipureintro; exact ⟨Hwc.1, osCoh_clearCut Hwc.2 Hml hnt hdur hb⟩

end specs

end Fs
end Perennial
