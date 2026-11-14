/- Lean-first (no Rocq counterpart).

# `Create`'s new WAL name, split out and registered (G-spine; `notes/wal-fsext-plan.md`, W1 log and
W4 log, fourteenth session)

After `Create`'s commit (the rename of `nm.tmp` onto `nm`, `walCreate_osAUnc`) the program and the
invariant hold half each of the creating claim `(jr, .only [nm, nm.tmp], h)`; a path to the new
directory `r/nm` needs a fraction of a claim on `nm` alone (`osPathS_child`). Two ghost steps, the lock
held by `Create` (a lock token `T`, so the creating map is empty, as `walInvBody_merge2`):

* `walInvBody_dropT`: `walInvBody_drop` with the lock held: the program gets the whole claim on
  `nm.tmp` (`.only [b]`), both keep half of the rest (`N.diff [b]`);
* `walInvBody_rekey`: a claim of the area holding a WAL name, rekeyed to a set of the same names
  (`N.diff [nm.tmp]` to `.only [nm]`, which `osPathS_child` needs): both halves, the invariant's claims
  changed by covering (`coverOk_rekey`);
* `walInv_splitNew`: both, at a program step;
* `walInvBody_register`: the WAL registered (`walNamesRes`): its name added to the split names (`Wn`,
  `walSplitFrag`, the program's area part), the pending registration back to `none`, and a fraction
  of the program's half of `(jr, .only [nm], hn)` given to the invariant (`nameShare`). After it the
  name's claim never changes again in the generation (its holders keep their fractions).

What stays open for `Create` (W4): the cleanup's rename of `r/nm` away (after a failed parent fsync)
needs the whole claim on `nm` back, before the registration (the invariant's half of an unregistered
name, `o = some dir`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateMergeStep
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.NameSplit
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSteps

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

open Classical in
/-- **Rekeying a claim of the area covers the claims**: same directory, same history, same names. -/
theorem coverOk_rekey {cl : List Claim} {jr : Ino} {D D' : NameSet} {hD : NamesH} {n : Nat}
    (hS : D.Same D') :
    CoverOk jr cl (replClaim (jr, D, hD) (jr, D', hD) cl) n := by
  let f : Claim → Claim := fun c => if c = (jr, D, hD) then (jr, D', hD) else c
  have hf1 : ∀ c, (f c).1 = c.1 := fun c => by
    simp only [f]; split <;> simp_all
  have hf3 : ∀ c, (f c).2.2 = c.2.2 := fun c => by
    simp only [f]; split <;> simp_all
  have hf2 : ∀ c b, c.2.1.Mem b ↔ (f c).2.1.Mem b := fun c b => by
    simp only [f]; split
    · rename_i hc; subst hc; exact hS b
    · exact Iff.rfl
  have hmem : ∀ c, c ∈ cl → f c ∈ replClaim (jr, D, hD) (jr, D', hD) cl := fun c hc =>
    List.mem_map_of_mem hc
  have hinv : ∀ c', c' ∈ replClaim (jr, D, hD) (jr, D', hD) cl → ∃ c ∈ cl, f c = c' := fun c' hc' =>
    List.mem_map.1 hc'
  have hfix : ∀ c, c.1 ≠ jr → f c = c := fun c hc => by
    simp only [f]; rw [if_neg]; rintro rfl; exact hc rfl
  refine ⟨fun m' hr => ?_, fun c hcj => ?_, fun c hcj ho => ?_, fun N h hm b hb _ => ?_,
    fun b _ N0 h0 hm0 hb => ?_⟩
  · obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
    refine (regionCrashed_iff _ _ _).2 ⟨K, regionCrashedK_cover (fun c hc x e E hx => ?_)
      (fun c hc b hb => ?_) hK⟩
    · exact ⟨f c, hmem c hc, E, by rw [hf3]; exact hx⟩
    · exact ⟨f c, hmem c hc, hf1 c, (hf2 c b).1 hb, fun K' => by rw [hf1, hf3]⟩
  · constructor
    · intro hc
      obtain ⟨y, hy, e⟩ := hinv c hc
      have hy1 : y.1 ≠ jr := by rw [← hf1, e]; exact hcj
      rw [hfix y hy1] at e; rw [← e]; exact hy
    · intro hc
      have := hmem c hc; rwa [hfix c hcj] at this
  · exact claimOnce_repl_other ho (fun he => hcj (by rw [he])) (fun he => hcj (by rw [he]))
  · obtain ⟨y, hy, e⟩ := hinv _ hm
    refine ⟨y.2.1, y.2.2, ?_, (hf2 y b).2 (by rw [e]; exact hb), by rw [← hf3 y, e]⟩
    have hy1 : y.1 = jr := by rw [← hf1, e]
    obtain ⟨y1, y2, y3⟩ := y
    simp only at hy1; subst hy1; exact hy
  · have e : ((jr, (f (jr, N0, h0)).2.1, (f (jr, N0, h0)).2.2) : Claim) = f (jr, N0, h0) := by
      have h1 := hf1 (jr, N0, h0)
      revert h1; generalize f (jr, N0, h0) = c; rintro rfl; rfl
    exact ⟨(f (jr, N0, h0)).2.1, (f (jr, N0, h0)).2.2, by rw [e]; exact hmem _ hm0, (hf2 _ b).1 hb⟩

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **A claim of the area holding a WAL name, rekeyed** (see the file header): the program's half of
`(jr, D, hD)` (the invariant's other half, `WalsCreateOk`, `osClaims_keys`; once), both halves rekeyed
to `D'`, the same names; the program holds a lock token (`T`), so the creating map is empty. -/
theorem walInvBody_rekey (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (D D' : NameSet) (hD : NamesH) (nm : GoString) (T : IProp GF)
    (hT : ⊢ T -∗ walUnlockedTok (W := W) -∗ False) {Em : CoPset}
    (hnm : walNameOk nm) (hDnm : D.Mem nm) (hS : D.Same D') (hE : ↑osShN ⊆ Em) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ osSharedInv (L := L) R -∗ T -∗
      osNames (L := L) jr D (DFrac.own (1 : Qp).half) hD ={Em}=∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ T ∗
        osNames (L := L) jr D' (DFrac.own (1 : Qp).half) hD := by
  classical
  have hDe : D ≠ .only [] := nameSet_ne_empty hDnm
  have hD'e : D' ≠ .only [] := nameSet_ne_empty ((hS nm).1 hDnm)
  unfold walInvBody
  iintro Hb #Hsi Ht H
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %hr, Hcl, Hn, HF, %hwo, %hwc, ⟨%CR, HCRa, %hCR⟩, Htl, %hab,
    %hwn, Hpk, ⟨%K, %cc, HK, Hcc, %hdk⟩, %hAt, Hnms, %Hbd⟩
  icases walCreating_empty CR T hT $$ HCRa Ht with ⟨%hCR0, HCRa, Ht⟩
  subst hCR0
  imod osClaims_keys R jr D _ hD _ hDe hE $$ Hsi H Hcl with ⟨H, Hcl, %hk⟩
  have hm : ((jr, D, hD) : Claim) ∈ cl := by
    obtain ⟨M, g, hm, hM⟩ := hwc nm hnm
    obtain ⟨e1, e2⟩ := hk ((jr, M, g), _) (List.mem_map_of_mem hm) rfl nm hDnm hM
    simp only at e1 e2
    rw [e1, e2] at hm; exact hm
  icases osClaims_once (L := L) cl (jr, D, hD) hDe hm $$ H Hcl with ⟨%ho, H, Hcl⟩
  obtain ⟨l1, l2, rfl, hl1, hl2⟩ := ho
  icases (osClaims_split (L := L) l1 l2 (jr, D, hD) _).1 $$ Hcl with ⟨H1, Hc0, H2⟩
  icases osNames_halves jr D hD hD hDe $$ H Hc0 with ⟨-, Hw⟩
  imod osNames_rekey (L := L) R jr D D' hD hS hE $$ Hsi Hw with Hw
  icases osNames_halve jr D' hD hD'e $$ Hw with ⟨Hh1, Hh2⟩
  have hcl' : replClaim (jr, D, hD) (jr, D', hD) (l1 ++ (jr, D, hD) :: l2) = l1 ++ (jr, D', hD) :: l2 :=
    replClaim_split hl1 hl2
  have hcov : CoverOk jr (l1 ++ (jr, D, hD) :: l2) (l1 ++ (jr, D', hD) :: l2) n := by
    rw [← hcl']; exact coverOk_rekey hS
  have hnW : ∀ c : Claim, c.1 = jr → ¬ WalDirClaimOf Ls c := fun c hc => hAt.not_walDirClaimOf c hc
  have hf : (l1 ++ (jr, D', hD) :: l2).filter (fun c : Claim => decide (c.1 ≠ jr)) =
      (l1 ++ (jr, D, hD) :: l2).filter (fun c : Claim => decide (c.1 ≠ jr)) := by
    rw [← hcl']; exact filter_replClaim _ (by simp) (by simp) _
  ihave Hpk := walParked_cover Ls jr _ _ hnW hf $$ Hpk
  imodintro
  iframe Ht Hh2
  iexists Ls, l1 ++ (jr, D', hD) :: l2, n, F
  iframe Hg Hn HF Htl Hpk Hnms
  isplitr
  · ipureintro; exact hr
  isplitl [H1 Hh1 H2]
  · iapply (osClaims_split (L := L) l1 l2 _ _).2
    iframe
  isplitr
  · ipureintro; exact walsOk_cover hcov hAt hwo
  isplitr
  · ipureintro; exact walsCreateOk_cover hcov hwc
  isplitl [HCRa]
  · iexists ∅
    iframe HCRa
    ipureintro; intro dir N' h' J' hl'; simp at hl'
  isplitr
  · ipureintro; exact ⟨absentNone_cover hcov hab.1, hab.2⟩
  isplitr
  · ipureintro; exact walsNamed_cover hcov hAt hwn
  isplitl [HK Hcc]
  · iexists K, cc
    iframe HK Hcc
    ipureintro; exact dirKeysOk_cover hcov hdk
  ipureintro; exact ⟨walsAt_cover hcov hwo hAt, Hbd⟩

/-- **The drop of the name `b` off an area claim, the lock held** (`walInvBody_drop` with a lock
token `T` in place of the free one; see the file header). -/
theorem walInvBody_dropT (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (N : NameSet) (h : NamesH) (nm b : GoString) (T : IProp GF)
    (hT : ⊢ T -∗ walUnlockedTok (W := W) -∗ False) {Em : CoPset}
    (hnm : walNameOk nm) (hNnm : N.Mem nm) (hb : N.Mem b) (hbw : walNameP b = false)
    (hbn : ¬ walNameOk b) (hbs : AreaSlot b) (hE : ↑osShN ⊆ Em) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ osSharedInv (L := L) R -∗
      T -∗ osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ={Em}=∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ T ∗
      osNames (L := L) jr (N.diff [b]) (DFrac.own (1 : Qp).half) (h.restrict jr (N.diff [b])) ∗
      osNames (L := L) jr (.only [b]) (DFrac.own 1) (h.restrict jr (N.inter [b])) := by
  classical
  have hNe : N ≠ .only [] := nameSet_ne_empty hb
  have hbnm : nm ≠ b := fun he => hbn (he ▸ hnm)
  have hDe : N.diff [b] ≠ .only [] :=
    nameSet_ne_empty ((N.mem_diff [b] nm).2 ⟨hNnm, by simpa using hbnm⟩)
  have hSame : (N.inter [b]).Same (.only [b]) := fun b' => by
    rw [N.mem_inter]
    simp only [NameSet.Mem, List.mem_singleton]
    constructor
    · exact fun h' => h'.2
    · rintro rfl; exact ⟨hb, rfl⟩
  unfold walInvBody
  iintro Hb #Hsi Ht H
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %hr, Hcl, Hn, HF, %hwo, %hwc, ⟨%CR, HCRa, %hCR⟩, Htl, %hab,
    %hwn, Hpk, ⟨%K, %cc, HK, Hcc, %hdk⟩, %hAt, Hnms, %Hbd⟩
  icases walCreating_empty CR T hT $$ HCRa Ht with ⟨%hCR0, HCRa, Ht⟩
  subst hCR0
  imod osClaims_log (L := L) R _ hE $$ Hsi Hcl with ⟨Hcl, %hlog⟩
  imod osClaims_keys R jr N _ h _ hNe hE $$ Hsi H Hcl with ⟨H, Hcl, %hkeys⟩
  imod osNames_self R jr N _ h hE $$ Hsi H with ⟨H, %hself⟩
  obtain ⟨N1, h1, hm1, hN1⟩ := hwc nm hnm
  obtain ⟨rfl, rfl⟩ := hkeys ((jr, N1, h1), _) (List.mem_map_of_mem hm1) rfl nm hNnm hN1
  have hd : DropOk cl jr N1 h1 b := by
    obtain ⟨log, hst, hl⟩ := hlog
    refine ⟨⟨log, hst, fun c hc x e Es hx => hl (c, _) (List.mem_map_of_mem hc) x e Es hx⟩, hm1,
      hself, hb, fun c hc hne hj hcb => hne ?_⟩
    obtain ⟨e1, e2⟩ := hkeys (c, _) (List.mem_map_of_mem hc) hj b hb hcb
    obtain ⟨c1, c2, c3⟩ := c
    simp only at hj e1 e2
    rw [hj, e1, e2]
  obtain ⟨l1, l2, rfl, hl1⟩ := List.split_first hm1
  icases (osClaims_split (L := L) l1 l2 (jr, N1, h1) _).1 $$ Hcl with ⟨H1, Hc0, H2⟩
  by_cases hl2 : (jr, N1, h1) ∈ l2
  · obtain ⟨m1, m2, rfl, -⟩ := List.split_first hl2
    icases (osClaims_split (L := L) m1 m2 (jr, N1, h1) _).1 $$ H2 with ⟨-, Hc1, -⟩
    iexfalso
    iapply osNames_three_halves jr N1 h1 h1 h1 hNe $$ H Hc0 Hc1
  have hW : ¬ WalDirClaimOf Ls (jr, N1, h1) := hAt.not_walDirClaimOf _ rfl
  icases osNames_halves jr N1 h1 h1 hNe $$ Hc0 H with ⟨-, Hw⟩
  imod osNames_split (L := L) R jr N1 [b] h1 hE $$ Hsi Hw with ⟨HI, HD⟩
  imod osNames_rekey (L := L) R jr (N1.inter [b]) (.only [b]) _ hSame hE $$ Hsi HI with HI
  icases osNames_halve jr (N1.diff [b]) _ hDe $$ HD with ⟨HD1, HD2⟩
  have hnW : ∀ c : Claim, c.1 = jr → ¬ WalDirClaimOf Ls c := fun c hc => hAt.not_walDirClaimOf c hc
  have hf : (dropClaims (l1 ++ (jr, N1, h1) :: l2) jr N1 h1 b).filter
      (fun c : Claim => decide (c.1 ≠ jr)) =
      (l1 ++ (jr, N1, h1) :: l2).filter (fun c : Claim => decide (c.1 ≠ jr)) := by
    unfold dropClaims; exact filter_replClaim _ (by simp) (by simp) _
  ihave Hpk := walParked_cover Ls jr _ _ hnW hf $$ Hpk
  have hw : ∀ dir d, s.wal !! dir = some d → ∃ lay nm, Ls !! dir = some lay ∧
      InArea s.area dir nm ∧ lay.jr = jr ∧ lay.nm = nm := fun dir d hd' => by
    obtain ⟨lay, nm', hj, hl, hia, hjr, hnm', -⟩ := hwo.1 dir d hd'
    exact ⟨lay, nm', hl, hia, hjr, hnm'⟩
  imodintro
  iframe Ht HI HD2
  iexists Ls, dropClaims (l1 ++ (jr, N1, h1) :: l2) jr N1 h1 b, n, F
  iframe Hg Hn HF Htl Hpk Hnms
  isplitr
  · ipureintro; exact hr
  isplitl [H1 HD1 H2]
  · unfold dropClaims
    rw [replClaim_split hl1 hl2]
    iapply (osClaims_split (L := L) l1 l2 _ _).2
    iframe
  isplitr
  · ipureintro; exact walsOk_drop hd hbw hbn hbs hab.2 hW hwo
  isplitr
  · ipureintro; exact walsCreateOk_drop hd.mem hbn hwc
  isplitl [HCRa]
  · iexists ∅
    iframe HCRa
    ipureintro; intro dir N' h' J' hl; simp at hl
  isplitr
  · ipureintro; exact ⟨absentNone_drop hd hbn hab.1, hab.2⟩
  isplitr
  · ipureintro; exact walsNamed_drop hd hbw hW hwn
  isplitl [HK Hcc]
  · iexists K, cc
    iframe HK Hcc
    ipureintro
    exact dirKeysOk_drop hd hbw hbn hw hdk
  ipureintro
  exact ⟨walsAt_drop hAt hd.mem, Hbd⟩

/-- **The new WAL registered** (see the file header): `Create`'s pending registration (`walNamesFrag
(some dir)`, its WAL present since a past state's) cleared, its name added to the split names, a
fraction `q` of a claim on the name alone (the invariant's other half, `osClaims_keys`; holding the
WAL's directory, `WalsAt`) given to the invariant. -/
theorem walInvBody_register (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s s0 : AbsDiskState) (dir nm : GoString) (Wn : List GoString) (q : Qp) (hn : NamesH) {Em : CoPset}
    (hin : InArea r dir nm) (hnok : NameOk nm) (hs0 : s0.wal !! dir ≠ none) (hE : ↑osShN ⊆ Em) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ osSharedInv (L := L) R -∗ walPast (W := W) s0 -∗
      walNamesFrag (W := W) (some dir) -∗ walSplitFrag (W := W) Wn -∗
      osNames (L := L) jr (.only [nm]) (DFrac.own q) hn ={Em}=∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ walNamesFrag (W := W) none ∗
        walSplitFrag (W := W) (nm :: Wn) := by
  have hnmM : (NameSet.only [nm]).Mem nm := by simp [NameSet.Mem]
  have hNe : NameSet.only [nm] ≠ .only [] := nameSet_ne_empty hnmM
  unfold walInvBody
  iintro Hb #Hsi #Hp Hf Hsf H
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %hr, Hcl, Hn, HF, %hwo, %hwc, HCR, Htl, %hab,
    %hwn, Hpk, Hdk, %hAt, Hnms, %Hbd⟩
  icases walPast_ghost_le s s0 $$ Hg Hp with %hle
  obtain ⟨d0, hd0⟩ := Option.ne_none_iff_exists'.1 hs0
  obtain ⟨d, hsd, -⟩ := hle.2.2 dir d0 hd0
  have hin' : InArea s.area dir nm := by rw [hr]; exact hin
  obtain ⟨lay, nm', -, hl, hin2, -, hnm', -⟩ := hwo.1 dir d hsd
  have e : nm' = nm := List.append_cancel_left (hin2.2.symm.trans hin'.2)
  subst e
  imod osClaims_keys R jr (.only [nm']) _ hn _ hNe hE $$ Hsi H Hcl with ⟨H, Hcl, %hk⟩
  have hm : ((jr, NameSet.only [nm'], hn) : Claim) ∈ cl := by
    obtain ⟨M, g, hm, hM⟩ := hwc nm' hin.1
    obtain ⟨e1, e2⟩ := hk ((jr, M, g), _) (List.mem_map_of_mem hm) rfl nm' hnmM hM
    simp only at e1 e2
    rw [e1, e2] at hm; exact hm
  unfold walNamesRes
  icases Hnms with ⟨%o, %Wn', Ha, Hs, %hf, Hsp, Hl⟩
  icases walNames_agree (W := W) o (some dir) $$ Ha Hf with %ho
  subst ho
  icases walSplit_agree (W := W) Wn' Wn $$ Hs Hsf with %hW
  subst hW
  imod walNames_set (W := W) (some dir) (some dir) none $$ Ha Hf with ⟨Ha, Hf⟩
  imod walSplit_set (W := W) Wn' Wn' (nm' :: Wn') $$ Hs Hsf with ⟨Hs, Hsf⟩
  imodintro
  iframe Hf Hsf
  iexists Ls, cl, n, F
  iframe Hg Hcl Hn HF HCR Htl Hpk Hdk
  isplitr
  · ipureintro; exact hr
  isplitr
  · ipureintro; exact hwo
  isplitr
  · ipureintro; exact hwc
  isplitr
  · ipureintro; exact hab
  isplitr
  · ipureintro; exact hwn
  isplitr
  · ipureintro; exact hAt
  isplitl
  rotate_left
  · ipureintro; exact Hbd
  iexists none, nm' :: Wn'
  iframe Ha Hs Hsp
  isplitr
  · ipureintro
    refine ⟨fun x hx => ?_, fun dir' lay' hl' _ => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨dir, lay, hl, hnm'⟩
      · exact hf.1 x hx
    · by_cases e : dir' = dir
      · subst e; rw [hl] at hl'; cases hl'; rw [hnm']; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hf.2 dir' lay' hl' (by simpa using Ne.symm e))
  iapply (BigSepL.bigSepL_cons (Φ := fun _ x => nameShare (L := L) jr Ls x)).2
  iframe Hl
  unfold nameShare
  iexists q, hn
  iframe H
  ipureintro
  refine ⟨hnok, hin.1, fun dir2 lay2 hl2 he2 => ?_⟩
  have := hAt.at hl2 hm (by rw [he2]; exact hnmM)
  rw [he2] at this; exact this

/-- `nm.tmp` dropped off `.only [nm, nm.tmp]` leaves the names of `.only [nm]`. -/
theorem only_diff_same (nm tmp : GoString) (hne : tmp ≠ nm) :
    ((NameSet.only [nm, tmp]).diff [tmp]).Same (.only [nm]) := fun b => by
  simp only [NameSet.diff, NameSet.Mem, List.mem_filter, List.mem_cons,
    List.not_mem_nil, or_false, decide_eq_true_eq]
  constructor
  · rintro ⟨rfl | rfl, h2⟩
    · rfl
    · exact absurd rfl h2
  · rintro rfl; exact ⟨Or.inl rfl, fun he => hne he.symm⟩

/-- **`Create`'s new name split out, at a program step** (see the file header): after the commit, the
program's half of the creating claim `(jr, .only [nm, nm.tmp], h)` becomes its half of a claim on `nm`
alone (the invariant's the other half) and the whole claim on `nm.tmp`. -/
theorem walInv_splitNew (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (nm tmp : GoString) (h : NamesH) (T : IProp GF) (hT : ⊢ T -∗ walUnlockedTok (W := W) -∗ False)
    (hnm : walNameOk nm) (hne : tmp ≠ nm) (htw : walNameP tmp = false) (htn : ¬ walNameOk tmp)
    (hts : AreaSlot tmp) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗ T -∗
      osNames (L := L) jr (.only [nm, tmp]) (DFrac.own (1 : Qp).half) h ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ T ∗
      osNames (L := L) jr (.only [nm]) (DFrac.own (1 : Qp).half)
        (h.restrict jr ((NameSet.only [nm, tmp]).diff [tmp])) ∗
      osNames (L := L) jr (.only [tmp]) (DFrac.own 1)
        (h.restrict jr ((NameSet.only [nm, tmp]).inter [tmp])) := by
  have hNnm : (NameSet.only [nm, tmp]).Mem nm := by simp [NameSet.Mem]
  have hNt : (NameSet.only [nm, tmp]).Mem tmp := by simp [NameSet.Mem]
  have hDnm : ((NameSet.only [nm, tmp]).diff [tmp]).Mem nm := (only_diff_same nm tmp hne nm).2 (by
    simp [NameSet.Mem])
  iintro #Hinv #Hsi Hnc Ht H
  iapply walInv_step C Mr R jr r
    iprop(osSharedInv (L := L) R ∗ T ∗
      osNames (L := L) jr (.only [nm, tmp]) (DFrac.own (1 : Qp).half) h)
    iprop(T ∗ osNames (L := L) jr (.only [nm]) (DFrac.own (1 : Qp).half)
        (h.restrict jr ((NameSet.only [nm, tmp]).diff [tmp])) ∗
      osNames (L := L) jr (.only [tmp]) (DFrac.own 1)
        (h.restrict jr ((NameSet.only [nm, tmp]).inter [tmp])))
    ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb ⟨#Hsi, Ht, H⟩
      imod walInvBody_dropT C Mr R jr r s (.only [nm, tmp]) h nm tmp T hT hnm hNnm hNt htw htn hts
        walN_osShN_top $$ Hb Hsi Ht H with ⟨Hb, Ht, HD, HT⟩
      imod walInvBody_rekey C Mr R jr r s _ (.only [nm]) _ nm T hT hnm hDnm (only_diff_same nm tmp hne)
        walN_osShN_top $$ Hb Hsi Ht HD with ⟨Hb, Ht, HD⟩
      imodintro
      iframe)
    $$ Hinv Hnc [Ht H]
  iframe Ht H; iexact Hsi

/-- **The new WAL registered, at a program step** (`walInvBody_register`). -/
theorem walInv_register (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s0 : AbsDiskState) (dir nm : GoString) (Wn : List GoString) (q : Qp) (hn : NamesH)
    (hin : InArea r dir nm) (hnok : NameOk nm) (hs0 : s0.wal !! dir ≠ none) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗ walPast (W := W) s0 -∗
      walNamesFrag (W := W) (some dir) -∗ walSplitFrag (W := W) Wn -∗
      osNames (L := L) jr (.only [nm]) (DFrac.own q) hn ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ walNamesFrag (W := W) none ∗
        walSplitFrag (W := W) (nm :: Wn) := by
  iintro #Hinv #Hsi Hnc #Hp Hf Hsf H
  iapply walInv_step C Mr R jr r
    iprop(osSharedInv (L := L) R ∗ walPast (W := W) s0 ∗ walNamesFrag (W := W) (some dir) ∗
      walSplitFrag (W := W) Wn ∗ osNames (L := L) jr (.only [nm]) (DFrac.own q) hn)
    iprop(walNamesFrag (W := W) none ∗ walSplitFrag (W := W) (nm :: Wn))
    ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb ⟨#Hsi, #Hp, Hf, Hsf, H⟩
      iapply walInvBody_register C Mr R jr r s s0 dir nm Wn q hn hin hnok hs0 walN_osShN_top
        $$ Hb Hsi Hp Hf Hsf H)
    $$ Hinv Hnc [Hf Hsf H]
  iframe Hf Hsf H
  isplitl []
  · iexact Hsi
  iexact Hp

end iris

end WalFs
end EtcdGrove
end Perennial

end
