/- Lean-first (no Rocq counterpart).

# `Discard`'s ghost steps (P6b state C, mit-pdos/etcd-grove#50; `notes/wal-p6-handoff.md`, session 15)

`wal.Discard` (`Spec/.../wal/Discard.lean`) renames the WAL's directory `r/nm` onto `r/nm.tmp` and fsyncs
the area. The rename needs one claim holding both names; as `Create`, it is the creating-claim shape
`.only [nm, tmp]`:
* a fresh WAL name outside the registered names (`exists_walName_notin`), to drop `nm.tmp` off the area
  claim (`walInv_drop`, which finds the invariant's half of the area claim through a WAL name in it);
* **U'**: the WAL's registered claim `(jr, .only [nm], hn)` (both halves) and the whole claim on `nm.tmp`
  merged into `(jr, .only [nm, tmp], hC)`, `nm` unregistered (`Wn.erase nm`) and the names state set to
  discarding `dir`;
* **R**: the rename's commit, `AU₁`;
* **S**: the area's fsync, `AU₂`, the WAL's layout removed.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.NameSplit

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

/-- **Some WAL name lies outside any list of names** (a string of `a`s longer than every name of `Wn`):
`Discard` drops `nm.tmp` off the area claim through it (`walInv_drop`'s WAL name `nm`; the WAL being
discarded is registered, so not in the area claim). -/
theorem exists_walName_notin (Wn : List GoString) : ∃ b, walNameOk b ∧ b ∉ Wn := by
  have hle : ∀ x ∈ Wn, x.length ≤ (Wn.map List.length).sum := by
    intro x hx
    induction Wn with
    | nil => cases hx
    | cons y ys ih =>
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · have := ih hx; simp only [List.map_cons, List.sum_cons]; omega
  refine ⟨List.replicate ((Wn.map List.length).sum + 1) (W8 97), ⟨?_, ?_, ?_⟩, ?_⟩
  · simp
  · intro h; have := List.eq_of_mem_replicate h; revert this; decide
  · intro h; have := List.eq_of_mem_replicate h; revert this; decide
  · intro hm
    have := hle _ hm
    simp at this; omega

section pure
variable [GooseExts]

/-- **Distinct layouts have distinct names** (each WAL's directory is its name's in the area). -/
theorem lay_nm_inj {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir dir' nm : GoString} {lay' : WalLay}
    (hok : WalsOk C Mr R jr s Ls cl n) (hin : InArea s.area dir nm) (hl' : Ls !! dir' = some lay')
    (hnm : lay'.nm = nm) : dir' = dir := by
  obtain ⟨d', hd'⟩ : ∃ d', s.wal !! dir' = some d' := by
    cases h' : s.wal !! dir' with
    | none => rw [hok.2.1 dir' h'] at hl'; cases hl'
    | some d => exact ⟨d, rfl⟩
  obtain ⟨l2, nm2, -, hl2, hin2, -, hnm2, -⟩ := hok.1 dir' d' hd'
  rw [hl'] at hl2; cases hl2
  rw [hin2.2, hin.2, ← hnm2, hnm]

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- With no loan out, the registered names' shares are all `0`; one registered name's taken out. -/
theorem nameShares_erase (jr : Ino) (Ls : GMap GoString WalLay) (Wn : List GoString) (nm : GoString)
    (hm : nm ∈ Wn) :
    ([∗list] k ↦ y ∈ Wn, nameShare (L := L) jr Ls y (shareLs Wn [] k y)) ⊢
      nameShare (L := L) jr Ls nm 0 ∗
        [∗list] k ↦ y ∈ Wn.erase nm, nameShare (L := L) jr Ls y (shareLs (Wn.erase nm) [] k y) := by
  simp only [shareLs_nil]
  exact (BigSepL.bigSepL_perm (Φ := fun y => nameShare (L := L) jr Ls y 0)
    (List.perm_cons_erase hm)).1.trans BigSepL.bigSepL_cons.1

/-- **Unregistering the WAL being discarded** (U', its names part): with the free lock token's names
fragment (no registration pending, no loan out) and the program's split names `Wn`, the present WAL at
`dir = r/nm` has its name registered; its claim's program half (the whole half: no loan) comes out of
`walNamesRes`, `nm` leaves the split names, and the names state records the discard (`disc = some dir`). -/
theorem walInvBody_unregister (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir nm : GoString) (Wn : List GoString) (hin : InArea r dir nm)
    (hsd : ∃ d, s.wal !! dir = some d) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walNamesFrag (W := W) none -∗
      walSplitFrag (W := W) Wn ==∗
      ∃ (hn : NamesH) (J : Ino), walInvBody (L := L) (W := W) C Mr R jr r s ∗
        walNamesFragS (W := W) ⟨none, some dir, []⟩ ∗ walSplitFrag (W := W) (Wn.erase nm) ∗
        osNames (L := L) jr (.only [nm]) (DFrac.own (1 : Qp).half) hn ∗
        ⌜nm ∈ Wn ∧ walNameOk nm ∧ NameOk nm ∧ hn.cur !! nm = some (.dir J)⌝ := by
  classical
  obtain ⟨d, hsd⟩ := hsd
  unfold walInvBody
  iintro Hb Hf Hsf
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %hr, Hcl, Hn, HF, %hwo, %hwc, HCR, Htl, %hab,
    %hwn, Hpk, HK, %hAt, Hnms, %Hbd⟩
  unfold walNamesRes
  icases Hnms with ⟨%st, %Wn', Ha, Hs, %hf, %hun, %hst, Hsp, Hl⟩
  icases walNamesS_agree (W := W) st _ $$ Ha Hf with %hst0
  subst hst0
  icases walSplit_agree (W := W) Wn' Wn $$ Hs Hsf with %hW0
  subst hW0
  have hin' : InArea s.area dir nm := by rw [hr]; exact hin
  obtain ⟨hm, lay, hl, hnm⟩ := split_present hwo hf.2 hin' hsd
  ihave Hl := nameShares_erase jr Ls Wn' nm hm $$ Hl
  icases Hl with ⟨H0, Hl⟩
  unfold nameShare
  icases H0 with ⟨%q, %hn, Hn0, %hq⟩
  obtain ⟨hqv, hnok, hwnm, hcur⟩ := hq
  have hq' : q = (1 : Qp).half := Subtype.ext (by rw [← hqv, Rat.add_zero])
  subst hq'
  imod walNamesS_set (W := W) _ _ ⟨none, some dir, []⟩ $$ Ha Hf with ⟨Ha, Hf⟩
  imod walSplit_set (W := W) _ _ (Wn'.erase nm) $$ Hs Hsf with ⟨Hs, Hsf⟩
  imodintro
  iexists hn, lay.j
  iframe Hf Hsf Hn0
  isplitl
  · iexists Ls, cl, n, F
    iframe Hg Hcl Hn HF HCR Htl Hpk HK
    isplitr; · ipureintro; exact hr
    isplitr; · ipureintro; exact hwo
    isplitr; · ipureintro; exact hwc
    isplitr; · ipureintro; exact hab
    isplitr; · ipureintro; exact hwn
    isplitr; · ipureintro; exact hAt
    isplitl
    · iexists ⟨none, some dir, []⟩, Wn'.erase nm
      iframe Ha Hs Hsp Hl
      isplitr
      · ipureintro
        refine ⟨fun y hy => hf.1 y (List.mem_of_mem_erase hy), fun dir' lay' hl' _ hd' => ?_⟩
        have hne : dir' ≠ dir := fun e => hd' (by rw [e])
        have hm' : lay'.nm ∈ Wn' := hf.2 dir' lay' hl' (by simp) (by simp)
        refine (List.mem_erase_of_ne (fun e => hne (lay_nm_inj hwo hin' hl' e))).2 hm'
      isplitr
      · ipureintro; intro dir' d' h'; cases h'
      ipureintro
      exact ⟨fun _ => rfl, fun x hx => by cases hx⟩
    ipureintro; exact Hbd
  ipureintro; exact ⟨hm, hwnm, hnok, hcur dir lay hl hnm⟩

/-- **U'** (`Discard`'s merge, at the invariant's contents): the WAL at `dir = r/nm` unregistered
(`walInvBody_unregister`), its claim's halves and the whole claim on `nm.tmp` merged into the claim
`(jr, .only [nm, tmp], hC)` (`walInvBody_mergeIn`, the free token less its names fragment for the
creating map's emptiness), the program's half of it out; of `tmp` it says what `tmp`'s claim did, of
`nm` the WAL's directory `J`. -/
theorem walInvBody_discardU (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir nm tmp : GoString) (Wn : List GoString) (hT : NamesH) {Em : CoPset}
    (hin : InArea r dir nm) (hsd : ∃ d, s.wal !! dir = some d) (htmp : ¬ walNameOk tmp)
    (hE : ↑osShN ⊆ Em) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ osSharedInv (L := L) R -∗
      walUnlockedTok (W := W) -∗ walSplitFrag (W := W) Wn -∗
      osNames (L := L) jr (.only [tmp]) (DFrac.own 1) hT ={Em}=∗
      ∃ (hC : NamesH) (J : Ino), walInvBody (L := L) (W := W) C Mr R jr r s ∗ walUnlockedTokX (W := W) ∗
        walNamesFragS (W := W) ⟨none, some dir, []⟩ ∗ walSplitFrag (W := W) (Wn.erase nm) ∗
        osNames (L := L) jr (.only [nm, tmp]) (DFrac.own (1 : Qp).half) hC ∗
        ⌜nm ∈ Wn ∧ hC.restrict jr (.only [tmp]) = hT.restrict jr (.only [tmp]) ∧
          hC.cur !! nm = some (.dir J)⌝ := by
  iintro Hb #Hsi Hu Hsf HT
  icases (walUnlockedTokX_join (W := W)).2 $$ Hu with ⟨Hx, Hf⟩
  imod walInvBody_unregister C Mr R jr r s dir nm Wn hin hsd $$ Hb Hf Hsf
    with ⟨%hn, %J, Hb, Hf, Hsf, Hn, %hp⟩
  obtain ⟨hm, hwnm, -, hcur⟩ := hp
  have hN1 : (NameSet.only [nm]).Mem nm := by simp [NameSet.Mem]
  have hN2 : (NameSet.only [tmp]).Mem tmp := by simp [NameSet.Mem]
  imod walInvBody_mergeIn C Mr R jr r s (.only [nm]) (.only [tmp]) (.only [nm, tmp]) hn hT nm tmp
    (walUnlockedTokX (W := W)) walUnlockedTokX_exclX hwnm hN1 hN2
    (fun b hb => by
      simp only [NameSet.Mem, List.mem_singleton] at hb
      rw [hb]; exact htmp)
    (fun b => by simp [NameSet.Mem]) hE
    $$ Hb Hsi Hx Hn HT with ⟨%hC, Hb, Hx, HC, %hmr⟩
  imodintro
  iexists hC, J
  iframe Hb Hx Hf Hsf HC
  ipureintro
  exact ⟨hm, hmr.2.1, (cur_of_part hmr.1 hN1).trans hcur⟩

/-- **U'** at a program step: the invariant opened (`notCrashed`), the WAL's presence read off the
client's first update (opened and aborted at once), `walInvBody_discardU`. -/
theorem walInv_discardU (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir nm tmp : GoString) (Wn : List GoString) (hT : NamesH) (ic : Nat)
    (Q₁ : WalDur → IProp GF) (hin : InArea r dir nm) (htmp : ¬ walNameOk tmp) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗
      (AU <{ ∃∃ d : WalDur, walDiskAtI (W := W) dir ic d }> @ walAuMask, ∅
        <{ walDiskAtI (W := W) dir (ic + 1) { d with named := false }, COMM Q₁ d }>) -∗
      walUnlockedTok (W := W) -∗ walSplitFrag (W := W) Wn -∗
      osNames (L := L) jr (.only [tmp]) (DFrac.own 1) hT ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗
      (AU <{ ∃∃ d : WalDur, walDiskAtI (W := W) dir ic d }> @ walAuMask, ∅
        <{ walDiskAtI (W := W) dir (ic + 1) { d with named := false }, COMM Q₁ d }>) ∗
      ∃ (hC : NamesH) (J : Ino), walUnlockedTokX (W := W) ∗
        walNamesFragS (W := W) ⟨none, some dir, []⟩ ∗ walSplitFrag (W := W) (Wn.erase nm) ∗
        osNames (L := L) jr (.only [nm, tmp]) (DFrac.own (1 : Qp).half) hC ∗
        ⌜nm ∈ Wn ∧ hC.restrict jr (.only [tmp]) = hT.restrict jr (.only [tmp]) ∧
          hC.cur !! nm = some (.dir J)⌝ := by
  iintro #Hinv #Hsi Hnc Hau Hu Hsf HT
  iapply walInv_step C Mr R jr r
    iprop(osSharedInv (L := L) R ∗
      (AU <{ ∃∃ d : WalDur, walDiskAtI (W := W) dir ic d }> @ walAuMask, ∅
        <{ walDiskAtI (W := W) dir (ic + 1) { d with named := false }, COMM Q₁ d }>) ∗
      walUnlockedTok (W := W) ∗ walSplitFrag (W := W) Wn ∗
      osNames (L := L) jr (.only [tmp]) (DFrac.own 1) hT)
    iprop((AU <{ ∃∃ d : WalDur, walDiskAtI (W := W) dir ic d }> @ walAuMask, ∅
        <{ walDiskAtI (W := W) dir (ic + 1) { d with named := false }, COMM Q₁ d }>) ∗
      ∃ (hC : NamesH) (J : Ino), walUnlockedTokX (W := W) ∗
        walNamesFragS (W := W) ⟨none, some dir, []⟩ ∗ walSplitFrag (W := W) (Wn.erase nm) ∗
        osNames (L := L) jr (.only [nm, tmp]) (DFrac.own (1 : Qp).half) hC ∗
        ⌜nm ∈ Wn ∧ hC.restrict jr (.only [tmp]) = hT.restrict jr (.only [tmp]) ∧
          hC.cur !! nm = some (.dir J)⌝)
    ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb ⟨#Hsi, Hau, Hu, Hsf, HT⟩
      -- read `dir`'s presence off the client's update, aborted at once
      have hsub : walAuMask ⊆ (⊤ : CoPset) \ ↑walN := by
        intro p hp
        exact LawfulSet.mem_diff.2 ⟨CoPset.mem_full, (LawfulSet.mem_diff.1 hp).2⟩
      imod (fupd_mask_subseteq hsub) with Hmc
      ihave Hacc := aupd_aacc $$ Hau
      unfold atomic_acc
      imod Hacc with Hacc
      isimp only [texist_cons, texist_nil] at Hacc
      icases Hacc with ⟨%d0, Hab0, Hcla⟩
      isimp only [Std.Tele.app, ULift.down] at Hab0
      iunfold walDiskAtI at Hab0
      iunfold walDirIsI at Hab0
      icases Hab0 with ⟨%M, %I, HM, HI, %HMd, %HI⟩
      iunfold walInvBody at Hb
      icases Hb with ⟨%Ls, %cl, %n, %F, Hg, Hrest⟩
      icases walOwn_agree s M $$ Hg HM with %HMs
      have hsd : ∃ d, s.wal !! dir = some d := by
        obtain ⟨d1, e1, -⟩ := (walOptLe_some_iff _ _).1 HMd
        have := HMs dir; rw [e1] at this
        obtain ⟨d2, e2, -⟩ := (walOptLe_some_iff _ _).1 this
        exact ⟨d2, e2⟩
      icases Hcla with ⟨Hab, -⟩
      imod Hab $$ [HM HI] with Hau
      · isimp only [Std.Tele.app, ULift.down]; iunfold walDiskAtI; iunfold walDirIsI; iexists M, I; iframe HM HI; ipureintro; exact ⟨HMd, HI⟩
      imod Hmc with -
      ihave Hb : walInvBody (L := L) (W := W) C Mr R jr r s $$ [Hg Hrest]
      · unfold walInvBody; iexists Ls, cl, n, F; iframe
      imod walInvBody_discardU C Mr R jr r s dir nm tmp Wn hT hin hsd htmp walN_osShN_top
        $$ Hb Hsi Hu Hsf HT with ⟨%hC, %J, Hb, Hrest⟩
      imodintro
      iframe Hb
      isplitl [Hau]
      · iexact Hau
      iexists hC, J
      iexact Hrest)
    $$ Hinv Hnc [Hau Hu Hsf HT]
  iframe Hau Hu Hsf HT; iexact Hsi

/-- **The ghost state at a changed real state with incarnations bumped** (R's and S's commits): all
five shares of the incarnations (`walGhostI`'s quarter, the program view's and the lock's quarters
`walIncQ`, the keys' authority's and the pipeline reserve's eighths `walIncE`) set to `I'`, the map to
the new state's, the past states grown by `walLeI` (`walLeI_unname`, `walLeI_discard`), the locked ranges
carried by `hlk`. -/
theorem walGhostI_bump (s s' : AbsDiskState) (I I' I1 I2 I3 I4 : GMap GoString Nat)
    (M : GMap GoString WalDur)
    (hle : walLeI (s, I) (s', I')) (hk : walKeysInArea s → walKeysInArea s')
    (hst : ∀ n, WalsStepped s n → WalsStepped s' n)
    (hlk : walLksAuth (W := W) s ⊢ walLksAuth (W := W) s') :
    ⊢@{IProp GF} walGhostI (W := W) s I -∗ walOwn (W := W) M -∗ walIncQ (W := W) I1 -∗
      walIncQ (W := W) I2 -∗ walIncE (W := W) I3 -∗ walIncE (W := W) I4 ==∗
      ⌜walMapLe M s.wal ∧ I1 = I ∧ I2 = I ∧ I3 = I ∧ I4 = I⌝ ∗ walGhostI (W := W) s' I' ∗
        walOwn (W := W) s'.wal ∗ walIncQ (W := W) I' ∗ walIncQ (W := W) I' ∗
        walIncE (W := W) I' ∗ walIncE (W := W) I' ∗ walPastI (W := W) (s', I') := by
  iintro Hc HM H1 H2 H3 H4
  imod preceipt_zero (GF := GF) with #H0
  unfold walGhostI walOwn walOwnAt walIncQ walIncE
  letI := walAllG (W := W)
  icases Hc with ⟨⟨%G, Hs, %HG⟩, ⟨HP, HI⟩, ⟨Hh, Hlk⟩, %Hk, #Hst⟩
  icases HM with ⟨HM, Ht⟩
  icases ghostVar_agree $$ HM Hs with %HMG
  subst HMG
  icases ghostVar_agree $$ H1 HI with %e1
  icases ghostVar_agree $$ H2 HI with %e2
  icases ghostVar_agree $$ H3 HI with %e3
  icases ghostVar_agree $$ H4 HI with %e4
  subst e1 e2 e3 e4
  imod ghostVar_update_halves s'.wal _ _ _ $$ Hs HM with ⟨Hs, HM⟩
  ihave H12 := (ghostVar_split_half W.γI (1 : Qp).half _).2 $$ [H1 H2]
  · iframe H1 H2
  ihave H34 := (ghostVar_split_half W.γI (1 : Qp).half.half _).2 $$ [H3 H4]
  · iframe H3 H4
  ihave HI4 := (ghostVar_split_half W.γI (1 : Qp).half _).2 $$ [HI H34]
  · iframe HI H34
  imod ghostVar_update_2 I' W.γI _ (1 : Qp).half _ (1 : Qp).half (Qp.half_add_half 1) $$ HI4 H12
    with ⟨HI4, H12⟩
  icases (ghostVar_split_half W.γI (1 : Qp).half I').1 $$ H12 with ⟨H1, H2⟩
  icases (ghostVar_split_half W.γI (1 : Qp).half I').1 $$ HI4 with ⟨HI, H34⟩
  icases (ghostVar_split_half W.γI (1 : Qp).half.half I').1 $$ H34 with ⟨H3, H4⟩
  ihave HP := walPastI_grow _ (s', I') hle $$ HP
  imod walPastI_snap (s', I') $$ HP with ⟨HP, Hp⟩
  ihave Hlk := hlk $$ Hlk
  ihave #Hst' := walStepsLb_upd s s' 0 (fun n hn => by rw [Nat.max_zero]; exact hst n hn) $$ H0 Hst
  imodintro
  iframe HM Ht HP HI Hh Hlk Hp Hs H1 H2 H3 H4 Hst'
  isplitr
  · ipureintro; exact ⟨HG, rfl, rfl, rfl, rfl⟩
  isplitr
  · ipureintro; exact walMapLe_refl _
  ipureintro; exact hk Hk

end iris

end WalFs
end EtcdGrove
end Perennial

end
