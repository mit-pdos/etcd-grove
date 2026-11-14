/- Lean-first (no Rocq counterpart).

# `Create`'s unminting (W4, `notes/wal-fsext-plan.md`, twenty-first session)

`renameWAL` failed before its commit (`renameWALPost`'s third arm): the minting is undone. The
creating entry goes, its token back as the free lock token (`walInv_unmint`); the program's halves of
the area claim less `nm` and of the creating claim `.only [nm, nm.tmp]` are merged (`walInv_merge2`,
the free token excluding a creating entry; the first holds a WAL name other than `nm`,
`walName_fresh`) and `nm.tmp` dropped off again (`walInv_drop`); `J`'s halves are joined and merged
with the pipeline's names (`create_Jback`) into what `nm.tmp`'s claim holds (`tmpDirH`). The area
claim's history is then not literally the one the abort began with (`h.restrict jr (N.diff
[nm.tmp])`), only one agreeing with it on its names' current entries, which is all the abort uses:
`create_abortTmpH` is `create_abortTmp` over such a history.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAbort
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TmpClaim
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAreaBack

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- A restriction keeps a directory's having only files. -/
theorem filesOnly_restrictN (N : NameSet) (e : Ents) (h : FilesOnly e) : FilesOnly (restrictN N e) := by
  intro c n hc
  by_cases hN : N.Mem c
  · rw [restrictN_lookup _ _ _ hN] at hc; exact h c n hc
  · rw [restrictN_lookup_not _ _ _ hN] at hc; cases hc

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- What a pipeline name holds is no directory. -/
theorem tmpEnt_noDir (o : Option Node) :
    tmpEnt (GF := GF) o ⊢ ⌜∀ n, o = some n → ∃ i, n = .file i⌝ := by
  rcases o with _ | ⟨i⟩ | ⟨j⟩
  · iintro -; ipureintro; intro n hn; cases hn
  · iintro -; ipureintro; intro n hn; cases hn; exact ⟨i, rfl⟩
  · unfold tmpEnt; iintro %h; exact h.elim

/-- **`J`'s claim back whole**: its claim off the pipeline's names (only files) merged with the
pipeline's two names (`walTmpsRes`, no directory), a claim on all of `J`'s names holding only files. -/
theorem create_Jback (R : Roots) (J : Ino) (hJ : NamesH) {E : CoPset} (hE : ↑osShN ⊆ E)
    (hfo : FilesOnly hJ.cur) :
    osSharedInv (L := hG.goose_localGS) R -∗
      osNames (L := hG.goose_localGS) J (.except walTmps) (DFrac.own 1) hJ -∗
      walTmpsRes (GF := GF) J ={E}=∗
      ∃ hJ' : NamesH, ⌜FilesOnly hJ'.cur ∧ hJ'.cur !! go!".touch" = hJ.cur !! go!".touch"⌝ ∗
        osNames (L := hG.goose_localGS) J (.except []) (DFrac.own 1) hJ' := by
  iintro #Hsi HD HT
  unfold walTmpsRes
  simp only [walTmps]
  unfold tmpClaim
  icases HT with ⟨⟨%h0, H0, He0⟩, ⟨%h1, H1, He1⟩, -⟩
  ihave %hf0 := tmpEnt_noDir _ $$ He0
  ihave %hf1 := tmpEnt_noDir _ $$ He1
  imod osNames_merge R J (.except [go!"0.tmp", go!"1.tmp"]) (.only [go!"0.tmp"])
    (.except [go!"1.tmp"]) hJ h0
    (fun b => by
      simp only [NameSet.Mem, List.mem_cons, List.mem_nil_iff, or_false, not_or]
      by_cases hb : b = go!"0.tmp" <;> simp [hb])
    hE $$ Hsi HD H0 with ⟨%ha, Ha, %hra⟩
  imod osNames_merge R J (.except [go!"1.tmp"]) (.only [go!"1.tmp"]) (.except []) ha h1
    (fun b => by
      simp only [NameSet.Mem, List.mem_cons, List.mem_nil_iff, or_false]
      by_cases hb : b = go!"1.tmp" <;> simp [hb])
    hE $$ Hsi Ha H1 with ⟨%hb, Hb, %hrb⟩
  imodintro
  iexists hb
  iframe Hb
  ipureintro
  refine ⟨?_, ?_⟩
  rotate_left
  · rw [cur_of_part hrb.1 (by simp [NameSet.Mem]), cur_of_part hra.1 (by simp [NameSet.Mem])]
  intro c n hc
  by_cases c1 : c = go!"1.tmp"
  · subst c1
    rw [cur_of_part hrb.2.1 (by simp [NameSet.Mem])] at hc
    exact hf1 n hc
  · rw [cur_of_part hrb.1 (by simp [NameSet.Mem, c1])] at hc
    by_cases c0 : c = go!"0.tmp"
    · subst c0
      rw [cur_of_part hra.2.1 (by simp [NameSet.Mem])] at hc
      exact hf0 n hc
    · rw [cur_of_part hra.1 (by simp [NameSet.Mem, c0, c1])] at hc
      exact hfo c n hc

/-- **`create_abortTmp` over any history of the area claim less `nm.tmp`** agreeing with
`h`'s on its names' current entries. -/
theorem create_abortTmpH (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (N : NameSet) (h : NamesH) (cl : List (GoString × Claim)) (nm : GoString) (hT : NamesH)
    (Wn : List GoString) (hok : AreaOk N h cl Wn) (hnm : walNameOk nm) (hNm : N.Mem nm)
    (hself : h.restrict jr N = h) (hN : NamesH)
    (hcur : ∀ b, (N.diff [tmpName nm]).Mem b → hN.cur !! b = h.cur !! b) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗ osSharedInv (L := hG.goose_localGS) R -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ walUnlockedTok (W := W) -∗
      osNames (L := hG.goose_localGS) jr (N.diff [tmpName nm]) (DFrac.own (1 : Qp).half) hN -∗
      tmpDirH jr (tmpName nm) hT -∗
      areaCls (L := hG.goose_localGS) (cl.filter (fun c => decide (c.1 ≠ tmpName nm))) -∗
      walSplitFrag (W := W) Wn ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ walUnlockedTok (W := W) ∗
        walAreaRes (L := hG.goose_localGS) jr := by
  iintro #Hinv #Hsi Hnc Hu HN Ht Hcl Hsf
  unfold tmpDirH
  icases Ht with ⟨HT, Hs⟩
  have hNnm : (N.diff [tmpName nm]).Mem nm :=
    (NameSet.mem_diff _ _ _).2 ⟨hNm, by simpa using (tmpName_ne nm).symm⟩
  imod walInv_mergeIn C Mr R jr r (N.diff [tmpName nm]) (.only [tmpName nm]) N
    hN hT nm (tmpName nm) (walUnlockedTok (W := W))
    walUnlockedTok_excl ⊤ CoPset.subseteq_top walN_osShN_top hnm hNnm (by simp [NameSet.Mem])
    (fun b hb => by simp only [NameSet.Mem, List.mem_singleton] at hb; subst hb; exact tmpName_not_walName nm)
    (fun b => by
      rw [NameSet.mem_diff]
      by_cases hb : b = tmpName nm
      · subst hb
        constructor
        · intro _; right; simp [NameSet.Mem]
        · intro _; exact areaOk_tmp hok hnm
      · simp [NameSet.Mem, hb])
    $$ Hinv Hsi Hnc Hu HN HT with ⟨Hnc, Hu, %h', HN, %hm⟩
  imod osNames_self R jr N _ h' CoPset.subseteq_top $$ Hsi HN with ⟨HN, %hself'⟩
  have htc : h'.cur !! tmpName nm = hT.cur !! tmpName nm :=
    cur_of_part hm.2.1 (by simp [NameSet.Mem] : (NameSet.only [tmpName nm]).Mem (tmpName nm))
  have hcb : ∀ b, b ≠ tmpName nm → h'.cur !! b = h.cur !! b := by
    intro b hb
    by_cases hNb : N.Mem b
    · have hmb : (N.diff [tmpName nm]).Mem b := (NameSet.mem_diff _ _ _).2 ⟨hNb, by simpa using hb⟩
      rw [cur_of_part hm.1 hmb, hcur b hmb]
    · have e1 : h'.cur !! b = none := by
        rw [← hself']; simp only [NamesH.restrict]; rw [restrictN_lookup_not _ _ _ hNb]
      have e2 : h.cur !! b = none := by
        rw [← hself]; simp only [NamesH.restrict]; rw [restrictN_lookup_not _ _ _ hNb]
      rw [e1, e2]
  imodintro
  iframe Hnc Hu
  iapply area_give N N h h' cl jr (tmpName nm) Wn hok (fun _ => Iff.rfl) (tmpName_not_walName nm)
    (fun b hb _ => hcb b hb)
  iframe HN Hcl Hsf
  rw [htc]
  iexact Hs

/-- **The unminting** (see the file header): from the creating entry, the program's halves of the
area claim less `nm` (as the minting left it) and of the creating claim, `J`'s halves and the
pipeline's names, the free lock token, the program's half of the area claim less `nm.tmp` (its names'
current entries `h`'s) and `nm.tmp`'s whole claim with what it holds. -/
theorem create_unmint (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r dir : GoString)
    (N : NameSet) (h : NamesH) (cl : List (GoString × Claim)) (Wn : List GoString) (nm : GoString)
    (hC : NamesH) (J : Ino) (hJ : NamesH)
    (hok : AreaOk N h cl Wn) (hnm : walNameOk nm) (hNnm : N.Mem nm) (hnmA : h.cur !! nm = none)
    (hctmp : hC.cur !! tmpName nm = some (.dir J)) (hcnm : hC.cur !! nm = none)
    (hfo : FilesOnly hJ.cur) (hJt : hJ.cur !! go!".touch" = none) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗ osSharedInv (L := hG.goose_localGS) R -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗
      walCreating (W := W) dir (.only [nm, tmpName nm]) hC J -∗
      osNames (L := hG.goose_localGS) jr ((N.diff [tmpName nm]).diff [nm]) (DFrac.own (1 : Qp).half)
        ((h.restrict jr (N.diff [tmpName nm])).restrict jr ((N.diff [tmpName nm]).diff [nm])) -∗
      osNames (L := hG.goose_localGS) jr (.only [nm, tmpName nm]) (DFrac.own (1 : Qp).half) hC -∗
      osNames (L := hG.goose_localGS) J (.except walTmps) (DFrac.own (1 : Qp).half) hJ -∗
      osNames (L := hG.goose_localGS) J (.except walTmps) (DFrac.own (1 : Qp).half) hJ -∗
      walTmpsRes (GF := GF) J ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ walUnlockedTok (W := W) ∗
        ∃ hN hT : NamesH, ⌜∀ b, (N.diff [tmpName nm]).Mem b → hN.cur !! b = h.cur !! b⌝ ∗
          osNames (L := hG.goose_localGS) jr (N.diff [tmpName nm]) (DFrac.own (1 : Qp).half) hN ∗
          tmpDirH jr (tmpName nm) hT := by
  iintro #Hinv #Hsi Hnc Hcr HNr HC HJ1 HJ2 HTs
  have hNt : N.Mem (tmpName nm) := areaOk_tmp hok hnm
  obtain ⟨b1, hb1, hb1L⟩ := walName_fresh (nm :: Wn)
  have hb1n : b1 ≠ nm := fun he => hb1L (by simp [he])
  have hb1W : b1 ∉ Wn := fun hm => hb1L (List.mem_cons_of_mem _ hm)
  have hb1t : b1 ≠ tmpName nm := fun he => tmpName_not_walName nm (he ▸ hb1)
  have hNb1 : N.Mem b1 := (hok.1 b1 hb1).resolve_right hb1W
  have hN1b1 : ((N.diff [tmpName nm]).diff [nm]).Mem b1 :=
    (NameSet.mem_diff _ _ _).2 ⟨(NameSet.mem_diff _ _ _).2 ⟨hNb1, by simpa using hb1t⟩,
      by simpa using hb1n⟩
  -- the creating entry off: the free lock token
  imod walInv_unmint C Mr R jr r dir _ _ J ⊤ CoPset.subseteq_top $$ Hinv Hnc Hcr with ⟨Hnc, Hu⟩
  -- the two halves merged into the program's half of a claim on `N`
  imod walInv_merge2 C Mr R jr r ((N.diff [tmpName nm]).diff [nm]) (.only [nm, tmpName nm]) N _ hC
    b1 nm (walUnlockedTok (W := W)) walUnlockedTok_excl ⊤ CoPset.subseteq_top walN_osShN_top hb1
    hN1b1 hnm (by simp [NameSet.Mem])
    (fun hm => ((NameSet.mem_diff _ _ _).1 hm).2 (List.mem_singleton_self _))
    (fun b => by
      rw [NameSet.mem_diff, NameSet.mem_diff]
      have e : (NameSet.only [nm, tmpName nm]).Mem b ↔ b = nm ∨ b = tmpName nm := by
        simp [NameSet.Mem]
      rw [e]
      constructor
      · intro hb
        by_cases e1 : b = nm
        · exact .inr (.inl e1)
        by_cases e2 : b = tmpName nm
        · exact .inr (.inr e2)
        exact .inl ⟨⟨hb, by simpa using e2⟩, by simpa using e1⟩
      · rintro (⟨⟨hb, -⟩, -⟩ | rfl | rfl)
        · exact hb
        · exact hNnm
        · exact hNt)
    $$ Hinv Hsi Hnc Hu HNr HC with ⟨Hnc, Hu, %h2, HN, %hm⟩
  -- `nm.tmp` off again, whole
  imod walInv_drop C Mr R jr r N h2 nm (tmpName nm) ⊤ CoPset.subseteq_top walN_osShN_top hnm hNnm
    hNt (tmpName_walNameP nm) (tmpName_not_walName nm) (tmpName_areaSlot hnm) $$ Hinv Hsi Hnc Hu HN
    with ⟨Hnc, Hu, HN, HT⟩
  -- `J`'s claim back whole
  ihave HJ : osNames (L := hG.goose_localGS) J (.except walTmps)
      (DFrac.own ((1 : Qp).half + (1 : Qp).half)) hJ $$ [HJ1 HJ2]
  · iapply (osNames_frac (L := hG.goose_localGS) J (.except walTmps) (1 : Qp).half (1 : Qp).half hJ).2
    iframe
  rw [Qp.half_add_half]
  imod create_Jback R J hJ CoPset.subseteq_top hfo $$ Hsi HJ HTs with ⟨%hJ', ⟨%hfo', %hJt'⟩, HJ⟩
  have h2t : h2.cur !! tmpName nm = some (.dir J) := by
    rw [cur_of_part hm.2.1 (by simp [NameSet.Mem] : (NameSet.only [nm, tmpName nm]).Mem (tmpName nm)),
      hctmp]
  imodintro
  iframe Hnc Hu
  iexists h2.restrict jr (N.diff [tmpName nm]), h2.restrict jr (N.inter [tmpName nm])
  iframe HN
  isplitr
  · ipureintro
    intro b hb
    simp only [NamesH.restrict]
    rw [restrictN_lookup _ _ _ hb]
    by_cases e : b = nm
    · subst e
      rw [cur_of_part hm.2.1 (by simp [NameSet.Mem] : (NameSet.only [b, tmpName b]).Mem b), hcnm, hnmA]
    · have hb1 : ((N.diff [tmpName nm]).diff [nm]).Mem b := (NameSet.mem_diff _ _ _).2 ⟨hb, by simpa using e⟩
      rw [cur_of_part hm.1 hb1]
      simp only [NamesH.restrict]
      rw [restrictN_lookup _ _ _ hb1, restrictN_lookup _ _ _ hb]
  unfold tmpDirH
  iframe HT
  have : (h2.restrict jr (N.inter [tmpName nm])).cur !! tmpName nm = some (.dir J) := by
    simp only [NamesH.restrict]
    rw [restrictN_lookup _ _ _ ((NameSet.mem_inter _ _ _).2 ⟨hNt, List.mem_singleton_self _⟩), h2t]
  rw [this]
  unfold tmpSub
  iexists hJ'
  iframe HJ
  rw [hJt', hJt]
  isplitr
  · ipureintro; exact hfo'
  unfold tmpEnt
  iempintro

end iris

end WalFs
end EtcdGrove
end Perennial

end
