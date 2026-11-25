/- Lean-first (no Rocq counterpart).

# `Discard`'s step S as an update of the WAL invariant (P6b state C, mit-pdos/etcd-grove#50;
`notes/wal-p6-handoff.md`, sessions 18-21)

After the area's fsync (`osCommitLb n`, past the rename, the last write of the WAL's name `nm` in the
program's claim `(jr, N, hC)`), the WAL in `dir` leaves the real state (`discS`) and the client's view
(`AU₂` committed: absent at incarnation `ic + 2`); its layout, its directory claim, its keys and its
tail record leave the invariant, and the program gets its directory's claim whole, its pipeline names'
claims and its others (`walInv_discardS`). The lock token's locked ranges are empty, so the locked
ranges carry over to the smaller state (`walGhostI_bump0`); its names fragment goes back to `none`
(`walNamesRes_discard`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DiscardSInv
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DiscardSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateNamedStep

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **`walGhostI_bump` with the lock token's empty locked ranges** (S: a WAL goes, so the locked ranges
carry over only because none is locked, `walTailsFrag T ∅`). -/
theorem walGhostI_bump0 (s s' : AbsDiskState) (I I' I1 I2 I3 I4 : GMap GoString Nat)
    (M : GMap GoString WalDur) (T : GMap GoString GName)
    (hle : walLeI (s, I) (s', I')) (hk : walKeysInArea s → walKeysInArea s')
    (hst : ∀ n, WalsStepped s n → WalsStepped s' n) :
    ⊢@{IProp GF} walGhostI (W := W) s I -∗ walOwn (W := W) M -∗ walIncQ (W := W) I1 -∗
      walIncQ (W := W) I2 -∗ walIncE (W := W) I3 -∗ walIncE (W := W) I4 -∗ walTailsFrag (W := W) T ∅ ==∗
      ⌜walMapLe M s.wal ∧ I1 = I ∧ I2 = I ∧ I3 = I ∧ I4 = I⌝ ∗ walGhostI (W := W) s' I' ∗
        walOwn (W := W) s'.wal ∗ walIncQ (W := W) I' ∗ walIncQ (W := W) I' ∗
        walIncE (W := W) I' ∗ walIncE (W := W) I' ∗ walPastI (W := W) (s', I') ∗
        walTailsFrag (W := W) T ∅ := by
  iintro Hc HM H1 H2 H3 H4 Hf
  imod preceipt_zero (GF := GF) with #H0
  unfold walGhostI walOwn walOwnAt walIncQ walIncE walLksAuth walTailsFrag
  letI := walAllG (W := W)
  icases Hc with ⟨⟨%G, Hs, %HG⟩, ⟨HP, HI⟩, ⟨Hh, ⟨%Lk, Hlk, -⟩⟩, %Hk, #Hst⟩
  icases Hf with ⟨Hft, Hfl⟩
  icases ghostVar_agree $$ Hlk Hfl with %eLk
  subst eLk
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
  ihave #Hst' := walStepsLb_upd s s' 0 (fun n hn => by rw [Nat.max_zero]; exact hst n hn) $$ H0 Hst
  imodintro
  iframe HM Ht HP HI Hh Hp Hs H1 H2 H3 H4 Hst' Hft Hfl
  isplitr
  · ipureintro; exact ⟨HG, rfl, rfl, rfl, rfl⟩
  iframe Hlk
  ipureintro; exact ⟨walMapLe_refl _, LksOk.empty _, hk Hk⟩

/-- A registered name's share, a layout removed. -/
theorem nameShare_delete (jr : Ino) (Ls : GMap GoString WalLay) (dir nm : GoString) (ls : Rat) :
    nameShare (L := L) jr Ls nm ls ⊢ nameShare (L := L) jr (GMap.delete dir Ls) nm ls := by
  unfold nameShare
  iintro ⟨%q, %hn, H, %h⟩
  iexists q, hn
  iframe H
  ipureintro
  refine ⟨h.1, h.2.1, h.2.2.1, fun d l hl hn' => h.2.2.2 d l ?_ hn'⟩
  by_cases e : d = dir
  · subst e; rw [GMap.lookup_delete_eq] at hl; cases hl
  · rwa [GMap.lookup_delete_ne _ (Ne.symm e)] at hl

/-- **The names state at the discard's end** (S): the discard recorded (`disc = some dir`, the program's
fragment) cleared, the WAL's layout gone; `dir`'s name `nm` is not registered (a registered name's share
and the program's area claim on `nm`, of another key, would share it). -/
theorem walNamesRes_discard (R : Roots) (jr : Ino) (r : GoString) (Ls : GMap GoString WalLay)
    (s s' : AbsDiskState) (dir nm : GoString) (lay : WalLay) (N : NameSet) (dq : DFrac) (hC : NamesH)
    (hl : Ls !! dir = some lay) (hnm : lay.nm = nm) (hN : N.Mem nm) (hNN : N ≠ .only [nm])
    {Em : CoPset} (hE : ↑osShN ⊆ Em) :
    ⊢ osSharedInv (L := L) R -∗ walNamesRes (L := L) (W := W) R jr r Ls s -∗
      walNamesFragS (W := W) ⟨none, some dir, []⟩ -∗ osNames (L := L) jr N dq hC ={Em}=∗
      walNamesRes (L := L) (W := W) R jr r (GMap.delete dir Ls) s' ∗ walNamesFrag (W := W) none ∗
        osNames (L := L) jr N dq hC := by
  unfold walNamesRes
  iintro #Hsi ⟨%st, %Wn, Ha, Hs, %hf, %hun, %hst, Hp, Hl⟩ Hf HC
  icases walNamesS_agree st _ $$ Ha Hf with %e
  subst e
  imod walNamesS_set _ _ ⟨none, none, []⟩ $$ Ha Hf with ⟨Ha, Hf⟩
  by_cases hm : nm ∈ Wn
  · ihave Hl := nameShares_erase (L := L) jr Ls Wn nm hm $$ Hl
    icases Hl with ⟨Hn, -⟩
    unfold nameShare
    icases Hn with ⟨%q, %hn, Hn, -⟩
    imod osNames_same_name R jr N (.only [nm]) dq _ hC hn nm hN (by simp [NameSet.Mem]) hE $$ Hsi HC Hn
      with ⟨%he, -, -⟩
    exact absurd he.1 hNN
  imodintro
  iframe Hf HC
  ihave Hl : ([∗list] k ↦ y ∈ Wn, nameShare (L := L) jr (GMap.delete dir Ls) y (shareLs Wn [] k y)) $$ [Hl]
  · iapply BigSepL.bigSepL_mono (fun {k y} _ => nameShare_delete (L := L) jr Ls dir y _) $$ Hl
  iexists ⟨none, none, []⟩, Wn
  iframe Ha Hs Hp Hl
  isplitr
  · ipureintro
    refine ⟨fun nm' hm' => ?_, fun dir' lay' hl' _ _ => ?_⟩
    · obtain ⟨dir', lay', hl', hn'⟩ := hf.1 nm' hm'
      by_cases e : dir' = dir
      · subst e; rw [hl] at hl'; cases hl'
        exact (hm (by rw [← hnm, hn']; exact hm')).elim
      · exact ⟨dir', lay', by rw [GMap.lookup_delete_ne _ (Ne.symm e)]; exact hl', hn'⟩
    · by_cases e : dir' = dir
      · subst e; rw [GMap.lookup_delete_eq] at hl'; cases hl'
      · rw [GMap.lookup_delete_ne _ (Ne.symm e)] at hl'
        exact hf.2 dir' lay' hl' (by simp) (by simpa using Ne.symm e)
  isplitr
  · ipureintro; intro _ _ h; cases h
  ipureintro; exact ⟨fun _ => rfl, fun x hx => by cases hx⟩

/-- **Two layouts never share a directory**, read off the parked state with the lock free. -/
theorem walParked_inj (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl) :
    ⊢ walParked (L := L) (W := W) Ls cl F -∗ walOutFrag (W := W) WalOut.empty -∗
      ⌜∀ dir1 dir2 (l1 l2 : WalLay), Ls !! dir1 = some l1 → Ls !! dir2 = some l2 → dir1 ≠ dir2 →
        l1.j ≠ l2.j⌝ ∗ walParked (L := L) (W := W) Ls cl F ∗ walOutFrag (W := W) WalOut.empty := by
  unfold walParked
  iintro ⟨%b, %o, Hpa, Hoa, %hp, Hs, Hc, Ht, Hw⟩ Ho
  icases walOut_agree (W := W) o _ $$ Hoa Ho with %ho
  subst ho
  have hT : WalOut.empty.T = [] := rfl
  simp only [hT]
  unfold walTmpParked
  icases Ht with ⟨Ht0, Hth⟩
  ihave Ht0 := walTmpParked0_inj Ls $$ Ht0
  icases Ht0 with ⟨%hd, Ht0⟩
  iframe Ho
  isplitr
  · ipureintro; exact hd
  iexists b, WalOut.empty
  simp only [hT]
  iframe Hpa Hoa Hs Hc Ht0 Hth Hw
  ipureintro; exact hp

/-- **S at a program step** (see the file header): after the area's fsync (`osCommitLb n` past `x`, the
rename's entry, the last write of `nm` in the program's area claim `(jr, N, hC)`, holding nothing there),
the WAL in `dir` discarded: `AU₂` committed, the free lock token back whole, and the WAL's directory
claim (whole), pipeline names and others to the program. -/
theorem walInv_discardS (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir nm : GoString) (N : NameSet) (hC : NamesH) (ic : Nat) (Q₂ : IProp GF)
    (x : Nat) (e : LogEntry) (Es : Ents) (n : Nat)
    (hin : InArea r dir nm) (hN : N.Mem nm) (hNN : N ≠ .only [nm]) (hR : RootsOk R)
    (hcur : hC.cur !! nm = none) (hlw : LastWrite hC jr nm x e Es) (hx : x < n)
    (hEs : Es !! nm = none) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗
      (AU <{ ∃∃ d : WalDur, walDiskAtI (W := W) dir (ic + 1) d }> @ walAuMask, ∅
        <{ walAbsentI (W := W) dir (ic + 2), COMM Q₂ }>) -∗
      walUnlockedTokX (W := W) -∗ walNamesFragS (W := W) ⟨none, some dir, []⟩ -∗
      osNames (L := L) jr N (DFrac.own (1 : Qp).half) hC -∗ osCommitLb (L := L) n ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ Q₂ ∗ walUnlockedTok (W := W) ∗
        osNames (L := L) jr N (DFrac.own (1 : Qp).half) hC ∗
        ∃ (J : Ino) (hj : NamesH), osNames (L := L) J (.except walTmps) (DFrac.own 1) hj ∗
          walTmpsRes (hG := ⟨G, L⟩) J ∗ walTmpsHalf (hG := ⟨G, L⟩) J ∗
          walOthers (L := L) [] J hj.cur ∗ ⌜J ≠ jr⌝ := by
  classical
  have hN0 : N ≠ .only [] := nameSet_ne_empty hN
  iintro #Hinv #Hsi Hnc Hau Hu Hnf Hn #Hc
  iapply walInv_stepS C Mr R jr r
    iprop(osSharedInv (L := L) R ∗
      (AU <{ ∃∃ d : WalDur, walDiskAtI (W := W) dir (ic + 1) d }> @ walAuMask, ∅
        <{ walAbsentI (W := W) dir (ic + 2), COMM Q₂ }>) ∗
      walUnlockedTokX (W := W) ∗ walNamesFragS (W := W) ⟨none, some dir, []⟩ ∗
      osNames (L := L) jr N (DFrac.own (1 : Qp).half) hC ∗ osCommitLb (L := L) n)
    iprop(Q₂ ∗ walUnlockedTok (W := W) ∗ osNames (L := L) jr N (DFrac.own (1 : Qp).half) hC ∗
        ∃ (J : Ino) (hj : NamesH), osNames (L := L) J (.except walTmps) (DFrac.own 1) hj ∗
          walTmpsRes (hG := ⟨G, L⟩) J ∗ walTmpsHalf (hG := ⟨G, L⟩) J ∗
          walOthers (L := L) [] J hj.cur ∗ ⌜J ≠ jr⌝)
    ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb ⟨#Hsi, Hau, Hu, Hnf, Hn, #Hc⟩
      unfold walInvBody
      icases Hb with ⟨%Ls, %cl, %n0, %F, Hg, %Har, Hcl0, #Hcm, Hlays, %Hok, %Hco, ⟨%CR, Hcra, %Hcro⟩,
        Htl, %Han, %Hnm, Hpk, ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
      -- the claims: the program's area claim the only one on `nm`, and one log
      imod osClaims_keys R jr N _ hC _ hN0 walN_osShN_top $$ Hsi Hn Hcl0 with ⟨Hn, Hcl0, %hkeys⟩
      imod osClaims_log R _ walN_osShN_top $$ Hsi Hcl0 with ⟨Hcl0, %hlog0⟩
      have hlog : ∃ log, Starts log ∧ ClaimsLog log cl := by
        obtain ⟨log, hs, hl⟩ := hlog0
        exact ⟨log, hs, fun c hc x e E hm => hl (c, _) (List.mem_map_of_mem hc) x e E hm⟩
      have honly : ∀ N' h', (jr, N', h') ∈ cl → N'.Mem nm → h' = hC := fun N' h' hm hN' =>
        (hkeys ((jr, N', h'), _) (List.mem_map_of_mem hm) rfl nm hN hN').2
      have hc : (jr, N, hC) ∈ cl := by
        obtain ⟨N', h', hc', hN'⟩ := Hco nm hin.1
        obtain ⟨e1, e2⟩ := hkeys ((jr, N', h'), _) (List.mem_map_of_mem hc') rfl nm hN hN'
        simp only at e1 e2
        rw [← e1, ← e2]; exact hc'
      -- the creating map is empty (the free token)
      icases walCreating_empty CR (walUnlockedTokX (W := W)) walUnlockedTokX_exclX $$ Hcra Hu
        with ⟨%hCR, Hcra, Hu⟩
      -- the client's view, and the five shares of the incarnations
      have hsub : walAuMask ⊆ (⊤ : CoPset) \ ↑walN := by
        intro p hp
        exact LawfulSet.mem_diff.2 ⟨CoPset.mem_full, (LawfulSet.mem_diff.1 hp).2⟩
      imod (fupd_mask_subseteq hsub) with Hmc
      ihave Hacc := aupd_aacc $$ Hau
      unfold atomic_acc
      imod Hacc with Hacc
      isimp only [texist_cons, texist_nil] at Hacc
      icases Hacc with ⟨%d0, Hab0, Hcla⟩
      irevert Hab0
      dsimp only [Std.Tele.app]
      iintro Hab0
      unfold walDiskAtI walDirIsI
      icases Hab0 with ⟨%M, %I1, HM, HI1, %HMd, %hI1⟩
      iunfold walGhost at Hg
      icases Hg with ⟨%I, Hg⟩
      unfold walUnlockedTokX walIncAny
      icases Hu with ⟨Ht1, Ht2, Ht3, Hof, Htf, %I2, HI2⟩
      icases walParked_incE Ls _ F $$ Hpk Hof with ⟨%I4, HI4, Hof, Hpk⟩
      icases walDirKeysAuth_bump K $$ Hdk with ⟨%I3, HI3, Hdk⟩
      have hle : walLeI (s, I) (discS s dir, <[dir := incOf I dir + 1]> I) := walLeI_discard s I dir
      imod walGhostI_bump0 s (discS s dir) I (<[dir := incOf I dir + 1]> I) I1 I2 I3 I4 M ∅ hle
        (fun hk k d hd => by
          by_cases e : k = dir
          · subst e; rw [discS_wal_eq] at hd; cases hd
          · rw [discS_wal_ne e] at hd; exact hk k d hd)
        (fun n' hn k d hd => by
          by_cases e : k = dir
          · subst e; rw [discS_wal_eq] at hd; cases hd
          · rw [discS_wal_ne e] at hd; exact hn k d hd)
        $$ Hg HM HI1 HI2 HI3 HI4 Htf with ⟨%he, Hg, HM, HI1, HI2, HI3, HI4, -, Htf⟩
      obtain ⟨HMs, e1, e2, e3, e4⟩ := he
      subst I1 I2 I3 I4
      obtain ⟨d1, e1, -⟩ := (walOptLe_some_iff _ _).1 HMd
      obtain ⟨ds, hsd, -⟩ := (walOptLe_some_iff _ _).1 (e1 ▸ HMs dir)
      ihave Hdk := Hdk $$ %(<[dir := incOf I dir + 1]> I) %(GMap.delete dir K) %(keys_bump I K dir) HI3
      ihave Hpk := Hpk $$ %(<[dir := incOf I dir + 1]> I) HI4
      -- `AU₂` committed
      icases Hcla with ⟨-, Hco2⟩
      isimp only [tforall_nil, Std.Tele.app, ULift.down] at Hco2
      imod Hco2 $$ [HM HI1] with HQ
      · iunfold walAbsentI
        iunfold walDirIsI
        iexists (discS s dir).wal, <[dir := incOf I dir + 1]> I
        iframe HM HI1
        ipureintro
        refine ⟨?_, ?_⟩
        · rw [discS_wal_eq]; exact trivial
        · rw [incOf_bump]; simp [hI1]
      imod Hmc with -
      -- the discarded WAL's layout and directory claim
      have hin' : InArea s.area dir nm := by rw [Har]; exact hin
      obtain ⟨lay, nm', -, hl, hin0, -, hnm', -⟩ := Hok.1 dir ds hsd
      have hlnm : lay.nm = nm := hnm'.trans (inArea_nm_inj hin' hin0)
      obtain ⟨X, hj, hok, hXe, hex⟩ := Hdko.2.2 dir lay hl
      subst hXe
      obtain ⟨hJr, hXn, honce, -, -⟩ := hok
      icases walParked_inj Ls _ F $$ Hpk Hof with ⟨%hdist, Hpk, Hof⟩
      have hs : DiscSet Ls cl jr dir lay (.except walTmps) hj :=
        ⟨hl, ⟨hlog, by obtain ⟨l1, l2, hcl, -, -⟩ := honce; rw [hcl]; simp, hex⟩,
          fun d' l' hl' hne => hdist d' dir l' lay hl' hl hne, hJr⟩
      have hW : WalDirClaimOf Ls (lay.j, .except walTmps, hj) := ⟨dir, lay, hl, rfl, walTmps, rfl, hXn⟩
      have hnone := discNone_of hin' hc hN honly hcur hlw (Nat.lt_of_lt_of_le hx (Nat.le_max_right n0 n)) hEs
      obtain ⟨hwo', hwc', hab', hwn', hdk', hat', hbd'⟩ :=
        discS_pure (n := max n0 n) (Nat.le_max_left _ _) hs hR hnone Hok Hco Han Hnm Hdko HAt Hbd
      -- its resources out
      icases (osClaims_filter_once (lay.j, NameSet.except walTmps, hj) cl _ honce).1 $$ Hcl0 with ⟨Hi, Hcl0⟩
      icases walParked_discard Ls cl F dir lay _ hl hW honce $$ Hpk Hof
        with ⟨Hpk, Hof, Hp2, Htr, Hth, Hoth⟩
      unfold laysResF
      ihave Hlays := segsAll_sep_delete (segResF (L := L) F) Ls dir lay hl $$ Hlays
      icases Hlays with ⟨-, Hlays⟩
      icases walTailsRes_discard C Mr s Ls F dir $$ Htl Htf with ⟨Htl, Htf⟩
      imod walNamesRes_discard R jr r Ls s (discS s dir) dir nm lay N _ hC hl hlnm hN hNN walN_osShN_top
        $$ Hsi Hnms Hnf Hn with ⟨Hnms, Hnf, Hn⟩
      icases osNames_halves lay.j (.except walTmps) hj hj (by intro h; cases h) $$ Hi Hp2 with ⟨-, Hw⟩
      imodintro
      isplitl [Hg Hcl0 Hlays Hcra Htl Hpk Hdk Hcp Hnms]
      · iexists discS s dir
        iexists GMap.delete dir Ls, dropC cl (lay.j, NameSet.except walTmps, hj), max n0 n, F
        isplitl [Hg]
        · iunfold walGhost; iexists _; iexact Hg
        isplitr
        · ipureintro; exact Har
        isplitl [Hcl0]
        · unfold dropC; iexact Hcl0
        isplitr
        · rcases Nat.le_total n0 n with hle | hle
          · rw [Nat.max_eq_right hle]; iexact Hc
          · rw [Nat.max_eq_left hle]; iexact Hcm
        isplitl [Hlays]
        · iexact Hlays
        isplitr
        · ipureintro; exact hwo'
        isplitr
        · ipureintro; exact hwc'
        isplitl [Hcra]
        · iexists CR
          iframe Hcra
          ipureintro; intro d N' h' J' hl'; rw [hCR] at hl'; simp at hl'
        isplitl [Htl]
        · iexact Htl
        isplitr
        · ipureintro; exact hab'
        isplitr
        · ipureintro; exact hwn'
        isplitl [Hpk]
        · iexact Hpk
        isplitl [Hdk Hcp]
        · iexists GMap.delete dir K, cp
          iframe Hdk Hcp
          ipureintro; exact hdk'
        isplitr
        · ipureintro; exact hat'
        iframe Hnms
        ipureintro; exact hbd'
      iframe HQ Hn
      isplitl [Ht1 Ht2 Ht3 Hof Htf HI2 Hnf]
      · iapply (walUnlockedTokX_join (W := W)).1
        iframe Hnf
        unfold walUnlockedTokX walIncAny
        iframe Ht1 Ht2 Ht3 Hof Htf
        iexists _; iexact HI2
      iexists lay.j, hj
      iframe Hw Htr Hth Hoth
      ipureintro; exact hJr)
    $$ Hinv Hnc [Hau Hu Hnf Hn]
  iframe Hau Hu Hnf Hn; iframe #

end iris

end WalFs
end EtcdGrove
end Perennial

end
