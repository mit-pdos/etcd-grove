/- Lean-first (no Rocq counterpart).

# `Create`'s area back after the commit (W4, nineteenth session)

After the commit, an error return (`renameWAL`'s arm 4) and the registration of the new name (`walInv_register`,
`nm` now in the split names) give `walAreaRes` back: the whole, now absent, claim on `nm.tmp` (`createSpR`'s)
merged back into the program's half of the rest of the area claim (`walInv_mergeIn`, the lock token held
excluding a free one), and `walAreaRes` rebuilt over the area's names less `nm` (`areaOk_reg`, `area_give`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAbort

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- A name `nm.sfx` is no WAL name (it holds a `.`). -/
theorem sfx_not_walName (nm sfx : GoString) : ¬ walNameOk (nm ++ go!"." ++ sfx) := by
  intro hw; apply hw.2.2; simp

/-- **The area with a WAL name registered**: `nm` out of the claim's names, into the split names. -/
theorem areaOk_reg {N : NameSet} {h : NamesH} {cl : List (GoString × Claim)} {Wn : List GoString}
    {nm : GoString} (hok : AreaOk N h cl Wn) (hnm : walNameOk nm) :
    AreaOk (N.diff [nm]) h cl (nm :: Wn) := by
  obtain ⟨a1, a2, a3, a4⟩ := hok
  refine ⟨fun b hb => ?_, fun b sfx hb => ?_, fun b hb hw => ?_, a4⟩
  · by_cases he : b = nm
    · exact .inr (by simp [he])
    · rcases a1 b hb with h1 | h1
      · exact .inl ((NameSet.mem_diff _ _ _).2 ⟨h1, by simpa using he⟩)
      · exact .inr (List.mem_cons_of_mem _ h1)
  · refine (NameSet.mem_diff _ _ _).2 ⟨a2 b sfx hb, ?_⟩
    simp only [List.mem_singleton]
    intro he
    exact sfx_not_walName b sfx (he ▸ hnm)
  · exact a3 b ((NameSet.mem_diff _ _ _).1 hb).1 hw

theorem List.le_sum_of_mem_nat {L : List GoString} {b : GoString} (hb : b ∈ L) :
    b.length ≤ (L.map List.length).sum := by
  induction L with
  | nil => cases hb
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hb with rfl | hb
    · omega
    · have := ih hb; omega

/-- A WAL name outside a finite list. -/
theorem walName_fresh (L : List GoString) : ∃ b, walNameOk b ∧ b ∉ L := by
  refine ⟨List.replicate ((L.map List.length).sum + 1) (W8 97), ⟨?_, ?_, ?_⟩, ?_⟩
  · simp
  · simp [List.mem_replicate]
  · simp [List.mem_replicate]
  · intro hm
    have := List.le_sum_of_mem_nat hm
    simp at this
    omega

/-- The merged claim says what the area said, off `nm.tmp` and the WAL names. -/
theorem areaBack_cur (N : NameSet) (h h' : NamesH) (jr : Ino) (nm tmp : GoString)
    (hself : h.restrict jr N = h) (hself' : h'.restrict jr (N.diff [nm]) = h')
    (h1 : h'.restrict jr ((N.diff [tmp]).diff [nm]) =
      ((h.restrict jr (N.diff [tmp])).restrict jr ((N.diff [tmp]).diff [nm])).restrict jr
        ((N.diff [tmp]).diff [nm]))
    (hnm : walNameOk nm) (b : GoString) (hb : b ≠ tmp) (hw : ¬ walNameOk b) :
    h'.cur !! b = h.cur !! b := by
  by_cases hN1 : ((N.diff [tmp]).diff [nm]).Mem b
  · rw [cur_of_part h1 hN1]
    have hN2 : (N.diff [tmp]).Mem b := ((NameSet.mem_diff _ _ _).1 hN1).1
    simp only [NamesH.restrict]
    rw [restrictN_lookup _ _ _ hN1, restrictN_lookup _ _ _ hN2]
  · have hbn : b ≠ nm := fun he => hw (he ▸ hnm)
    have hnd : ¬ (N.diff [nm]).Mem b := fun hm => hN1 (by
      obtain ⟨hm1, hm2⟩ := (NameSet.mem_diff _ _ _).1 hm
      exact (NameSet.mem_diff _ _ _).2 ⟨(NameSet.mem_diff _ _ _).2 ⟨hm1, by simpa using hb⟩, hm2⟩)
    have e1 : h'.cur !! b = none := by
      rw [← hself']; simp only [NamesH.restrict]; rw [restrictN_lookup_not _ _ _ hnd]
    have hNb : ¬ N.Mem b := fun hm => hnd ((NameSet.mem_diff _ _ _).2 ⟨hm, by simpa using hbn⟩)
    have e2 : h.cur !! b = none := by
      rw [← hself]; simp only [NamesH.restrict]; rw [restrictN_lookup_not _ _ _ hNb]
    rw [e1, e2]

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- See the file header: with the lock held (`T`), the new name registered (`nm :: Wn`). -/
theorem create_areaBack (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (N : NameSet) (h : NamesH) (cl : List (GoString × Claim)) (nm : GoString) (ht : NamesH)
    (Wn : List GoString) (T : IProp GF) (hT : ⊢ T -∗ walUnlockedTok (W := W) -∗ False)
    (hok : AreaOk N h cl Wn) (hnm : walNameOk nm) (hself : h.restrict jr N = h)
    (hft : ht.cur !! tmpName nm = none) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗ osSharedInv (L := hG.goose_localGS) R -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ T -∗
      osNames (L := hG.goose_localGS) jr ((N.diff [tmpName nm]).diff [nm]) (DFrac.own (1 : Qp).half)
        ((h.restrict jr (N.diff [tmpName nm])).restrict jr ((N.diff [tmpName nm]).diff [nm])) -∗
      osNames (L := hG.goose_localGS) jr (.only [tmpName nm]) (DFrac.own 1) ht -∗
      areaCls (L := hG.goose_localGS) (cl.filter (fun c => decide (c.1 ≠ tmpName nm))) -∗
      walSplitFrag (W := W) (nm :: Wn) ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ T ∗ walAreaRes (L := hG.goose_localGS) jr := by
  iintro #Hinv #Hsi Hnc Ht HN HT Hcl Hsf
  obtain ⟨b1, hb1, hb1L⟩ := walName_fresh (nm :: Wn)
  have hb1nm : b1 ≠ nm := fun he => hb1L (by simp [he])
  have hb1N : N.Mem b1 := (hok.1 b1 hb1).resolve_right (fun hm => hb1L (List.mem_cons_of_mem _ hm))
  have hb1t : b1 ≠ tmpName nm := fun he => tmpName_not_walName nm (he ▸ hb1)
  have hN1 : ((N.diff [tmpName nm]).diff [nm]).Mem b1 :=
    (NameSet.mem_diff _ _ _).2 ⟨(NameSet.mem_diff _ _ _).2 ⟨hb1N, by simpa using hb1t⟩,
      by simpa using hb1nm⟩
  have hNt := areaOk_tmp hok hnm
  imod walInv_mergeIn C Mr R jr r ((N.diff [tmpName nm]).diff [nm]) (.only [tmpName nm]) (N.diff [nm])
    _ ht b1 (tmpName nm) T hT ⊤ CoPset.subseteq_top walN_osShN_top hb1 hN1 (by simp [NameSet.Mem])
    (fun b hb => by simp only [NameSet.Mem, List.mem_singleton] at hb; subst hb; exact tmpName_not_walName nm)
    (fun b => by
      rw [NameSet.mem_diff, NameSet.mem_diff, NameSet.mem_diff]
      have e1 : (NameSet.only [tmpName nm]).Mem b ↔ b = tmpName nm := by simp [NameSet.Mem]
      rw [e1]
      simp only [List.mem_singleton]
      by_cases hb : b = tmpName nm
      · subst hb
        have := tmpName_ne nm
        constructor
        · intro _; right; rfl
        · intro _; exact ⟨hNt, this⟩
      · constructor
        · rintro ⟨h1, h2⟩; left; exact ⟨⟨h1, hb⟩, h2⟩
        · rintro (⟨⟨h1, _⟩, h2⟩ | h1)
          · exact ⟨h1, h2⟩
          · exact absurd h1 hb)
    $$ Hinv Hsi Hnc Ht HN HT with ⟨Hnc, Ht, %h', HN, %hm⟩
  imod osNames_self R jr (N.diff [nm]) _ h' CoPset.subseteq_top $$ Hsi HN with ⟨HN, %hself'⟩
  have htc : h'.cur !! tmpName nm = none := by
    have e := cur_of_part hm.2.1 (by simp [NameSet.Mem] : (NameSet.only [tmpName nm]).Mem (tmpName nm))
    rw [e, hft]
  imodintro
  iframe Hnc Ht
  iapply area_give (N.diff [nm]) (N.diff [nm]) h h' cl jr (tmpName nm) (nm :: Wn) (areaOk_reg hok hnm)
    (fun _ => Iff.rfl) (tmpName_not_walName nm)
    (fun b hb hw => areaBack_cur N h h' jr nm (tmpName nm) hself hself' hm.1 hnm b hb hw)
  iframe HN Hcl Hsf
  rw [htc]
  simp only [tmpSub]
  iempintro

end iris

end WalFs
end EtcdGrove
end Perennial

end
