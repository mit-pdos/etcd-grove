/- Lean-first (no Rocq counterpart).

# `Create`'s minting step (W4, `notes/wal-fsext-plan.md`, "W4 implementation log", eighth to tenth
sessions)

`walInvBody_mint`: after `nm.tmp` is dropped off the area claim (`walInvBody_drop`), created as the
directory `J` and filled (the program holding `nm.tmp`'s claim and `J`'s wholly), and before the
rename: the WAL name `nm` is split off the program's area claim (both halves: the invariant's is found
by `WalsCreateOk` and `osClaims_keys`, once by `osClaims_once`), merged with `nm.tmp`'s claim into the
creating claim `(jr, .only [nm, nm.tmp], hC)`, and both parts halved, the invariant keeping one half
of each (`mintClaims`, which covers the old claims: `coverOk_mint`). The creating token
`walCreating dir (.only [nm, nm.tmp]) hC J` is minted with the free lock token (`walCreating_mint`),
and `CreatingOk` recorded of its entry: the shared invariant's facts the rename's commit cannot open
(`osNames_coh`: the claim coherent; `osClaims_excl`: no other claim of the area holds `nm.tmp`, none of
`J` holds a `.wal` name, so `J` is not the area directory).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateMergeStep

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

theorem walNameP_dotwal [GooseExts] : walNameP go!".wal" = true := by
  unfold walNameP
  exact decide_eq_true (List.suffix_refl _)

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The minting** (see the file header). The program: the free lock token, its half of the area
claim `(jr, N, h)` (holding the WAL name `nm`, not `tmp`, with names besides `nm`), `tmp`'s claim
whole, `J`'s claim whole (on all names but `X`, which holds neither `nm` nor a `.wal` name). It gets
the creating token, its halves of the area claim off `nm` and of the creating claim, `J`'s claim
back, and what the creating claim says: of `tmp` what `tmp`'s did, of `nm` what the area claim did,
its log bound the larger of theirs. -/
theorem walInvBody_mint (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir nm tmp : GoString) (N : NameSet) (h hT : NamesH) (J : Ino)
    (X : List GoString) (hJ : NamesH) {Em : CoPset}
    (hnm : walNameOk nm) (hNnm : N.Mem nm) (hNt : ¬ N.Mem tmp) (hDe : N.diff [nm] ≠ .only [])
    (htmp : ¬ walNameOk tmp) (htw : walNameP tmp = false) (hXnm : nm ∉ X)
    (hX : ∀ b ∈ X, walNameP b = false) (hE : ↑osShN ⊆ Em) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ osSharedInv (L := L) R -∗
      walUnlockedTok (W := W) -∗ osNames (L := L) jr N (DFrac.own (1 : Qp).half) h -∗
      osNames (L := L) jr (.only [tmp]) (DFrac.own 1) hT -∗
      osNames (L := L) J (.except X) (DFrac.own 1) hJ ={Em}=∗
      ∃ hC, walInvBody (L := L) (W := W) C Mr R jr r s ∗
        walCreating (W := W) dir (.only [nm, tmp]) hC J ∗
        osNames (L := L) jr (N.diff [nm]) (DFrac.own (1 : Qp).half) (h.restrict jr (N.diff [nm])) ∗
        osNames (L := L) jr (.only [nm, tmp]) (DFrac.own (1 : Qp).half) hC ∗
        osNames (L := L) J (.except X) (DFrac.own 1) hJ ∗
        ⌜hC.restrict jr (.only [tmp]) = hT.restrict jr (.only [tmp]) ∧
          hC.restrict jr (N.inter [nm]) = h.restrict jr (N.inter [nm]) ∧
          hC.next = max (h.restrict jr (N.inter [nm])).next hT.next⌝ := by
  classical
  have hNe : N ≠ .only [] := nameSet_ne_empty hNnm
  have hTm : (NameSet.only [tmp]).Mem tmp := by simp [NameSet.Mem]
  have hTe : NameSet.only [tmp] ≠ .only [] := nameSet_ne_empty hTm
  have hXm : (NameSet.except X).Mem nm := hXnm
  have hXe : NameSet.except X ≠ .only [] := nameSet_ne_empty hXm
  have hCnm : (NameSet.only [nm, tmp]).Mem nm := by simp [NameSet.Mem]
  have hCe : NameSet.only [nm, tmp] ≠ .only [] := nameSet_ne_empty hCnm
  have hNC : ∀ b, (NameSet.only [nm, tmp]).Mem b ↔ (N.inter [nm]).Mem b ∨ (NameSet.only [tmp]).Mem b := by
    intro b
    rw [N.mem_inter]
    simp only [NameSet.Mem, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl ⟨hNnm, rfl⟩
      · exact Or.inr rfl
    · rintro (⟨-, rfl⟩ | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  unfold walInvBody
  iintro Hb #Hsi Hu H HT HJ
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %hr, Hcl, Hn, HF, %hwo, %hwc, ⟨%CR, HCRa, %hCR⟩, Htl, %hab,
    %hwn, Hpk, ⟨%K, %cc, HK, Hcc, %hdk⟩, %hAt, Hnms, %Hbd⟩
  -- what the shared invariant says of the claims held wholly, and of the area claim
  imod osClaims_excl (L := L) R cl J (.except X) hJ hXe hE $$ Hsi HJ Hcl with ⟨%hJx, HJ, Hcl⟩
  imod osClaims_excl (L := L) R cl jr (.only [tmp]) hT hTe hE $$ Hsi HT Hcl with ⟨%hTx, HT, Hcl⟩
  imod osClaims_keys R jr N _ h _ hNe hE $$ Hsi H Hcl with ⟨H, Hcl, %hk⟩
  have hm : ((jr, N, h) : Claim) ∈ cl := by
    obtain ⟨M, g, hm, hM⟩ := hwc nm hnm
    obtain ⟨e1, e2⟩ := hk ((jr, M, g), _) (List.mem_map_of_mem hm) rfl nm hNnm hM
    simp only at e1 e2
    rw [e1, e2] at hm; exact hm
  have hJjr : J ≠ jr := fun e => hJx (jr, N, h) hm e.symm nm hXm hNnm
  icases osClaims_once (L := L) cl (jr, N, h) hNe hm $$ H Hcl with ⟨%ho, H, Hcl⟩
  obtain ⟨l1, l2, hl, hl1, hl2⟩ := ho
  ihave Hcl := (show osClaims L (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) ⊢
      osClaims L (l1.map (fun c => (c, DFrac.own (1 : Qp).half))) ∗
        osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ∗
        osClaims L (l2.map (fun c => (c, DFrac.own (1 : Qp).half))) from by
    rw [hl]; exact (osClaims_split (L := L) l1 l2 _ _).1) $$ Hcl
  icases Hcl with ⟨Hl1, Hc0, Hl2⟩
  -- the area claim whole, `nm` split off, merged with `tmp`'s
  icases osNames_halves jr N h h hNe $$ H Hc0 with ⟨-, Hw⟩
  imod osNames_self R jr N _ h hE $$ Hsi Hw with ⟨Hw, %hself⟩
  imod osNames_split (L := L) R jr N [nm] h hE $$ Hsi Hw with ⟨HI, HD⟩
  imod osNames_self R jr (N.inter [nm]) _ _ hE $$ Hsi HI with ⟨HI, %hIself⟩
  imod osNames_merge (L := L) R jr (N.inter [nm]) (.only [tmp]) (.only [nm, tmp]) _ hT hNC hE
    $$ Hsi HI HT with ⟨%hC, HC, %hmr⟩
  imod osNames_coh R jr (.only [nm, tmp]) _ hC hE $$ Hsi HC with ⟨HC, %hcoh⟩
  icases osNames_halve jr (.only [nm, tmp]) hC hCe $$ HC with ⟨HC1, HC2⟩
  icases osNames_halve jr (N.diff [nm]) _ hDe $$ HD with ⟨HD1, HD2⟩
  have hCr : hC.restrict jr (N.inter [nm]) = h.restrict jr (N.inter [nm]) := hmr.1.trans hIself
  -- the creating token
  imod walCreating_mint CR dir (.only [nm, tmp]) hC J $$ HCRa Hu with ⟨%hCR0, HCRa, Htok⟩
  subst hCR0
  -- the new claims
  have hcov : CoverOk jr cl (mintClaims cl jr N h nm tmp hC) n :=
    coverOk_mint hm hself hNnm hCr htmp
  have hcl' : mintClaims cl jr N h nm tmp hC =
      replClaim (jr, N, h) (jr, N.diff [nm], h.restrict jr (N.diff [nm])) (l1 ++ (jr, N, h) :: l2) ++
        [(jr, .only [nm, tmp], hC)] := by
    rw [← hl]; rfl
  have hcl'' : mintClaims cl jr N h nm tmp hC =
      (l1 ++ (jr, N.diff [nm], h.restrict jr (N.diff [nm])) :: l2) ++ [(jr, .only [nm, tmp], hC)] := by
    rw [hcl', replClaim_split hl1 hl2]
  have hCm : ((jr, NameSet.only [nm, tmp], hC) : Claim) ∈ mintClaims cl jr N h nm tmp hC := by
    rw [hcl'']; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hTt : ∀ c ∈ cl, c.1 = jr → ¬ c.2.1.Mem tmp := fun c hc hj => hTx c hc hj tmp hTm
  have hcok : CreatingOk jr (mintClaims cl jr N h nm tmp hC)
      (<[dir := (NameSet.only [nm, tmp], hC, J)]> (∅ : GMap GoString (NameSet × NamesH × Ino))) := by
    intro dir' N' h' J' hl'
    by_cases hd : dir' = dir
    · subst hd
      rw [GMap.lookup_insert_eq] at hl'
      simp only [Option.some.injEq, Prod.mk.injEq] at hl'
      obtain ⟨rfl, rfl, rfl⟩ := hl'
      refine ⟨hCm, hcoh, ?_, ?_, ?_, ?_⟩
      · intro c hc hne hj b hb hcb
        rcases mem_mintClaims hc with he | he | ⟨hc', hne'⟩
        · exact hne he
        · rw [he] at hcb
          have h1 := (N.mem_diff [nm] b).1 hcb
          simp only [NameSet.Mem, List.mem_cons, List.mem_singleton, List.not_mem_nil,
            or_false] at hb
          rcases hb with rfl | rfl
          · exact h1.2 (List.mem_singleton_self _)
          · exact hNt h1.1
        · simp only [NameSet.Mem, List.mem_cons, List.mem_singleton, List.not_mem_nil,
            or_false] at hb
          rcases hb with rfl | rfl
          · obtain ⟨e1, e2⟩ := hk (c, _) (List.mem_map_of_mem hc') hj b hNnm hcb
            apply hne'
            obtain ⟨c1, c2, c3⟩ := c
            simp only at hj e1 e2
            rw [hj, e1, e2]
          · exact hTt c hc' hj hcb
      · refine ⟨l1 ++ (jr, N.diff [nm], h.restrict jr (N.diff [nm])) :: l2, [], by rw [hcl''], ?_,
          List.not_mem_nil⟩
        intro hm'
        rcases List.mem_append.1 hm' with h1 | h1
        · exact hTt _ (by rw [hl]; exact List.mem_append_left _ h1) rfl (by simp [NameSet.Mem])
        · rcases List.mem_cons.1 h1 with h1 | h1
          · simp only [Prod.mk.injEq, true_and] at h1
            have := (N.mem_diff [nm] nm).1 (h1.1 ▸ hCnm)
            exact this.2 (List.mem_singleton_self _)
          · exact hTt _ (by rw [hl]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1)) rfl
              (by simp [NameSet.Mem])
      · intro d2 J2 hd2
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hd2)]
        simp
      · refine ⟨hJjr, fun c hc hj b hb => ?_, fun d2 x hd2 hx => ?_, go!".wal", walNameP_dotwal, ?_⟩
        · have hc' : c ∈ cl := (hcov.other c (by rw [hj]; exact hJjr)).1 hc
          refine hJx c hc' hj b ?_
          show b ∉ X
          intro hbX
          rw [hX b hbX] at hb
          cases hb
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hd2)] at hx
          simp at hx
        · simp only [NameSet.Mem, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
            not_or]
          refine ⟨fun e => ?_, fun e => ?_⟩
          · have h1 := walNameP_false_of_ok hnm
            rw [← e, walNameP_dotwal] at h1
            cases h1
          · rw [← e, walNameP_dotwal] at htw
            cases htw
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hd)] at hl'
      simp at hl'
  have hnW : ∀ c : Claim, c.1 = jr → ¬ WalDirClaimOf Ls c := fun c hc => hAt.not_walDirClaimOf c hc
  have hf := filter_mintClaims (fun c : Claim => decide (c.1 ≠ jr)) (jr := jr) (N := N) (h := h)
    (nm := nm) (tmp := tmp) (hC := hC) (by simp) cl
  ihave Hpk := walParked_cover Ls jr _ _ hnW hf $$ Hpk
  imodintro
  iexists hC
  iframe Htok HD2 HC2 HJ
  isplitl [Hg Hl1 HD1 Hl2 HC1 Hn HF HCRa Htl Hpk HK Hcc Hnms]
  · iexists Ls, mintClaims cl jr N h nm tmp hC, n, F
    iframe Hg Hn HF Htl Hpk
    isplitr
    · ipureintro; exact hr
    isplitl [Hl1 HD1 Hl2 HC1]
    · rw [hcl']
      iapply osClaims_create (L := L) l1 l2 (jr, N, h) _ _ _ hl1 hl2
      iframe
    isplitr
    · ipureintro; exact walsOk_cover hcov hAt hwo
    isplitr
    · ipureintro; exact walsCreateOk_cover hcov hwc
    isplitl [HCRa]
    · iexists <[dir := (NameSet.only [nm, tmp], hC, J)]> (∅ : GMap GoString (NameSet × NamesH × Ino))
      iframe HCRa
      ipureintro; exact hcok
    isplitr
    · ipureintro; exact ⟨absentNone_cover hcov hab.1, hab.2⟩
    isplitr
    · ipureintro; exact walsNamed_cover hcov hAt hwn
    isplitl [HK Hcc]
    · iexists K, cc
      iframe HK Hcc
      ipureintro; exact dirKeysOk_cover hcov hdk
    iframe Hnms; ipureintro; exact ⟨walsAt_cover hcov hwo hAt, Hbd⟩
  ipureintro; exact ⟨hmr.2.1, hCr, hmr.2.2⟩

end iris

end WalFs
end EtcdGrove
end Perennial

end
