/- Lean-first (no Rocq counterpart).

# `Create`'s cleanup after its commit (W4, `notes/wal-units/create.md`)

`Create`'s deferred `cleanupWAL` (`WAL.cleanupWAL.spec`) runs on its three error exits after the
commit (the parent's `OpenDir`, `Fsync` or `Close` failed). Its frame (`createFr`) is what `Create`
holds of the area past the commit: the area's path, the program's half of the area claim less
`nm.tmp` and `nm`, its fraction `c` of the program's half of `nm`'s claim (the rest is in the two
pinned paths `Close` returns), the area's tagged claims and the split names. Its outcome when the
rename was called (`createFin`): the area's path, the call permission, the tail lock's closed file, and
the area less `nm.tmp` (`createAreaL`: its names as before but `nm` and a broken name), from which,
with `nm.tmp`'s claim merged back, `walAreaRes` (`create_cleanBack`).

* `create_cleanupLaw`: the rename's law (`cleanupLaw`). The program's half of `nm`'s claim whole
  again from the pinned paths (`os.osPathS_unchild` twice), merged back into the area claim
  (`walInv_merge2`), the merged claim pinned (`walInv_pinClean`, the token deposited), the rename in it
  through `cleanAU` (`CleanupAu.lean`: a rename that took effect is the moved-aside step); after any
  outcome, `createFin` (an unused update committed with no effect, `osAUnc_none'`).
* `create_cleanBack`: `nm.tmp`'s claim merged back (`walInv_mergeIn`), `walAreaRes` rebuilt
  (`area_give`, the broken name exempt: `BrokenSlot`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cleanupWAL
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAreaBack
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CleanupAu
public import Proof.os.MkdirAllParts

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
variable [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- The free lock token less its names fragment excludes a free one (both hold the lock's token). -/
theorem walUnlockedTokX_unlocked_excl :
    ⊢@{IProp GF} walUnlockedTokX (W := W) -∗ walUnlockedTok (W := W) -∗ False := by
  unfold walUnlockedTokX walUnlockedTok
  letI := walAllG (W := W)
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply token_exclusive $$ H1 H2

/-- **What `Create` lends its cleanup** (see the file header). -/
def createFr (R : Roots) (jr : Ino) (r nm : GoString) (qa : DFrac) (N : NameSet) (h : NamesH)
    (c : Qp) (hn : NamesH) (cl : List (GoString × Claim)) (Wn : List GoString) : IProp GF :=
  iprop(osPathS (L := hG.goose_localGS) R r qa jr ∗
    osNames (L := hG.goose_localGS) jr ((N.diff [tmpName nm]).diff [nm]) (DFrac.own (1 : Qp).half)
      ((h.restrict jr (N.diff [tmpName nm])).restrict jr ((N.diff [tmpName nm]).diff [nm])) ∗
    osNames (L := hG.goose_localGS) jr (.only [nm]) (DFrac.own c) hn ∗
    areaCls (L := hG.goose_localGS) (cl.filter (fun c => decide (c.1 ≠ tmpName nm))) ∗
    walSplitFrag (W := W) Wn)

/-- **The area less `nm.tmp`, after the cleanup's rename was called** (see the file header): the area
claim's names but `nm.tmp`, each as before (`h`) but `nm` and a broken name (`BrokenSlot`). -/
def createAreaL (jr : Ino) (nm : GoString) (N : NameSet) (h : NamesH) (cl : List (GoString × Claim))
    (Wn : List GoString) : IProp GF :=
  iprop(walUnlockedTokX (W := W) ∗
    ∃ h' : NamesH, osNames (L := hG.goose_localGS) jr (N.diff [tmpName nm]) (DFrac.own (1 : Qp).half) h' ∗
      areaCls (L := hG.goose_localGS) (cl.filter (fun c => decide (c.1 ≠ tmpName nm))) ∗
      walSplitFrag (W := W) Wn ∗
      ⌜∀ b, (N.diff [tmpName nm]).Mem b → b ≠ nm → ¬ BrokenSlot b → h'.cur !! b = h.cur !! b⌝)

/-- **What `Create` gets back from its cleanup's rename** (see the file header). -/
def createFin (R : Roots) (jr : Ino) (r nm : GoString) (qa : Qp) (f : Loc) (N : NameSet) (h : NamesH)
    (cl : List (GoString × Claim)) (Wn : List GoString) (_err : GoInterface) : IProp GF :=
  iprop(osPathS (L := hG.goose_localGS) R r (DFrac.own qa) jr ∗ osCallPerm (L := hG.goose_localGS) (callKey R r) 1 ∗
    (∃ nmf : GoString, os.ownFile f (-1 : w64) nmf (DFrac.own 1)) ∗
    createAreaL (W := W) jr nm N h cl Wn)

/-- The broken name is in the area claim's names but `nm.tmp`, and none of `nm`, `nm.tmp`. -/
theorem brokenName_facts {N : NameSet} {h : NamesH} {cl : List (GoString × Claim)} {Wn : List GoString}
    {nm ts : GoString} (hok : AreaOk N h cl Wn) (hnm : walNameOk nm) :
    (N.diff [tmpName nm]).Mem (brokenName nm ts) ∧ nm ≠ brokenName nm ts ∧
      ¬ walNameOk (brokenName nm ts) ∧ AreaSlot (brokenName nm ts) ∧ BrokenSlot (brokenName nm ts) := by
  have e : brokenName nm ts = nm ++ go!"." ++ (go!"broken." ++ ts) := by
    simp [brokenName, List.append_assoc]
  have hbs : BrokenSlot (brokenName nm ts) := ⟨nm, ts, hnm, rfl⟩
  refine ⟨(NameSet.mem_diff _ _ _).2 ⟨by rw [e]; exact hok.2.1 nm _ hnm, ?_⟩, fun he => ?_,
    by rw [e]; exact sfx_not_walName _ _, ⟨nm, hnm, .inr ⟨_, e⟩⟩, hbs⟩
  · simp only [List.mem_singleton]
    intro he; exact tmpName_not_broken hnm (he ▸ hbs)
  · have := congrArg List.length he; simp [brokenName] at this

/-- The merged claim says of the names but `nm` what the area claim said. -/
theorem merged_cur {jr : Ino} {N : NameSet} {h h' : NamesH} {nm : GoString}
    (hm : h'.restrict jr ((N.diff [tmpName nm]).diff [nm]) =
      ((h.restrict jr (N.diff [tmpName nm])).restrict jr ((N.diff [tmpName nm]).diff [nm])).restrict jr
        ((N.diff [tmpName nm]).diff [nm]))
    (b : GoString) (hb : (N.diff [tmpName nm]).Mem b) (hbn : b ≠ nm) : h'.cur !! b = h.cur !! b := by
  have hN1 : ((N.diff [tmpName nm]).diff [nm]).Mem b :=
    (NameSet.mem_diff _ _ _).2 ⟨hb, by simpa using hbn⟩
  rw [cur_of_part hm hN1]
  simp only [NamesH.restrict]
  rw [restrictN_lookup _ _ _ hN1, restrictN_lookup _ _ _ hb]

/-- **The cleanup's rename law** (see the file header). -/
theorem create_cleanupLaw [os.fileStat.FieldAssumptions] (Mr : WalMarshal) (R : Roots) (jr : Ino) (r nm : GoString) (qa : Qp)
    (N : NameSet) (h : NamesH) (cl : List (GoString × Claim)) (Wn : List GoString) (c d : Qp)
    (hn : NamesH) (J : Ino) (f : Loc)
    (hok : AreaOk N h cl Wn) (hnm : walNameOk nm) (hNnm : N.Mem nm) (hnmO : NameOk nm)
    (hcd : d + (d + c) = (1 : Qp).half) (hJ : hn.cur !! nm = some (.dir J)) :
    ⊢ walAreaOk (L := hG.goose_localGS) (W := W) walCodec Mr R jr r -∗
      cleanupLaw (W := W) R jr r nm R d f (createFr (W := W) R jr r nm (DFrac.own qa) N h c hn cl Wn)
        (createFin (W := W) R jr r nm qa f N h cl Wn) := by
  classical
  iintro #Hok
  unfold cleanupLaw
  iintro %ts %hts Hfr Hu Hnf ⟨%j, Hp1, Hp2⟩ Hf Hnc
  unfold walAreaOk
  icases Hok with ⟨#Hinv, #Hos, #Hsi, -, -⟩
  unfold createFr
  icases Hfr with ⟨Hp, HA, Hn, Hcl, Hsf⟩
  -- the two pinned paths give back their fractions of `nm`'s claim
  icases os.osPathS_unchild R r nm jr j d qa hnmO $$ [Hp1 Hp] with ⟨%hn1, Hp, Hn1, %-⟩
  · iframe
  icases os.osPathS_unchild R r nm jr j d (d + qa) hnmO $$ [Hp2 Hp] with ⟨%hn2, Hp, Hn2, %-⟩
  · iframe
  icases osNames_agree jr (.only [nm]) _ _ hn1 hn $$ Hn1 Hn with %e1
  subst e1
  icases osNames_agree jr (.only [nm]) _ _ hn2 hn1 $$ Hn2 Hn with %e2
  subst e2
  ihave Hnm := (osNames_frac (L := hG.goose_localGS) jr (.only [nm]) d c hn2).2 $$ [Hn2 Hn]
  · iframe
  ihave Hnm := (osNames_frac (L := hG.goose_localGS) jr (.only [nm]) d (d + c) hn2).2 $$ [Hn1 Hnm]
  · iframe
  rw [hcd]
  -- `nm`'s claim merged back into the area claim, the merge pinned
  obtain ⟨b1, hb1, hb1L⟩ := walName_fresh (nm :: Wn)
  have hb1nm : b1 ≠ nm := fun he => hb1L (by simp [he])
  have hb1N : N.Mem b1 := (hok.1 b1 hb1).resolve_right (fun hm => hb1L (List.mem_cons_of_mem _ hm))
  have hb1t : b1 ≠ tmpName nm := fun he => tmpName_not_walName nm (he ▸ hb1)
  have hN1b1 : ((N.diff [tmpName nm]).diff [nm]).Mem b1 :=
    (NameSet.mem_diff _ _ _).2 ⟨(NameSet.mem_diff _ _ _).2 ⟨hb1N, by simpa using hb1t⟩,
      by simpa using hb1nm⟩
  have hnmT : (N.diff [tmpName nm]).Mem nm :=
    (NameSet.mem_diff _ _ _).2 ⟨hNnm, by simpa using (tmpName_ne nm).symm⟩
  imod walInv_merge2 walCodec Mr R jr r ((N.diff [tmpName nm]).diff [nm]) (.only [nm]) (N.diff [tmpName nm])
    _ hn2 b1 nm (walUnlockedTokX (W := W)) walUnlockedTokX_exclX ⊤ CoPset.subseteq_top walN_osShN_top
    hb1 hN1b1 hnm (by simp [NameSet.Mem])
    (fun hm => ((NameSet.mem_diff _ _ _).1 hm).2 (List.mem_singleton_self _))
    (fun b => by
      rw [NameSet.mem_diff (N.diff [tmpName nm])]
      have e1 : (NameSet.only [nm]).Mem b ↔ b = nm := by simp [NameSet.Mem]
      rw [e1]
      by_cases hb : b = nm
      · subst hb; exact ⟨fun _ => Or.inr rfl, fun _ => hnmT⟩
      · simp only [List.mem_singleton, hb, not_false_eq_true, and_true, or_false])
    $$ Hinv Hsi Hnc Hu HA Hnm with ⟨Hnc, Hu, %h', HA, %hm⟩
  have hJ' : h'.cur !! nm = some (.dir J) := by
    rw [cur_of_part hm.2.1 (by simp [NameSet.Mem] : (NameSet.only [nm]).Mem nm), hJ]
  have hb1N' : (N.diff [tmpName nm]).Mem b1 := ((NameSet.mem_diff _ _ _).1 hN1b1).1
  imod walInv_pinClean walCodec Mr R jr r (N.diff [tmpName nm]) h' b1 hb1 hb1N' $$ Hinv Hsi Hnc Hu HA
    with ⟨Hnc, Hpin, HA⟩
  imod osNames_next R jr _ _ h' CoPset.subseteq_top $$ Hsi HA with ⟨HA, #Hlb⟩
  obtain ⟨hbN, hne, hbrk, hbS, hbB⟩ := brokenName_facts (ts := ts) hok hnm
  have hin : InArea r (child r nm) nm := ⟨hnm, by simp [child, List.append_assoc]; rfl⟩
  ihave Hau := cleanAU walCodec Mr R jr r (child r nm) nm (brokenName nm ts) (N.diff [tmpName nm]) h' J
    h'.next hin hne hnmT hbN hJ' (Nat.le_refl _) hbrk hbS $$ Hinv [Hpin Hnf]
  · unfold cleanP; iframe
  imodintro
  iframe Hnc
  iexists J, N.diff [tmpName nm], d + (d + qa), h', (1 : Qp).half, (1 : Qp).half, h'.next,
    cleanQ (W := W) (child r nm)
  iframe Hp Hlb HA Hau
  isplitr
  · ipureintro; exact ⟨hnmT, hbN, hJ', Qp.half_add_half 1⟩
  have hcur' : ∀ b, (N.diff [tmpName nm]).Mem b → b ≠ nm → h'.cur !! b = h.cur !! b :=
    merged_cur hm.1
  iintro %err Hnc Hp Hcp Hout
  -- what `Create` gets back, whatever the outcome
  have hfin : ∀ h'' : NamesH,
      (∀ b, (N.diff [tmpName nm]).Mem b → b ≠ nm → ¬ BrokenSlot b → h''.cur !! b = h.cur !! b) →
      ⊢ notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗
        osPathS (L := hG.goose_localGS) R r (DFrac.own (d + (d + qa))) jr -∗
        osCallPerm (L := hG.goose_localGS) (callKey R r) 1 -∗
        (∃ nmf : GoString, os.ownFile f (-1 : w64) nmf (DFrac.own 1)) -∗
        areaCls (L := hG.goose_localGS) (cl.filter (fun c => decide (c.1 ≠ tmpName nm))) -∗
        walSplitFrag (W := W) Wn -∗ walUnlockedTokX (W := W) -∗
        osNames (L := hG.goose_localGS) jr (N.diff [tmpName nm]) (DFrac.own (1 : Qp).half) h'' ={⊤}=∗
        notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗
          createFin (W := W) R jr r nm qa f N h cl Wn err := by
    intro h'' hh''
    iintro Hnc Hp Hcp Hf Hcl Hsf Hu HA
    icases (osPathS_frac (L := hG.goose_localGS) R r d (d + qa) jr).1 $$ Hp with ⟨-, Hp⟩
    icases (osPathS_frac (L := hG.goose_localGS) R r d qa jr).1 $$ Hp with ⟨-, Hp⟩
    imodintro
    iframe Hnc
    unfold createFin createAreaL
    iframe Hp Hcp Hf Hu
    iexists h''
    iframe HA Hcl Hsf
    ipureintro; exact hh''
  icases Hout with (⟨%herr, HA, Hau⟩ | ⟨%o, %ho, HQ, HA⟩)
  · imod osAUnc_none' _ _ _ (show osNames (L := hG.goose_localGS) jr (N.diff [tmpName nm])
        (DFrac.own (1 : Qp).half) h' ⊢ renDirOutA jr J (N.diff [tmpName nm]) nm (brokenName nm ts) h'
          (DFrac.own (1 : Qp).half) h'.next none from by
        unfold renDirOutA
        simp only [logOut, claimOut]
        iintro H
        iframe H
        ipureintro; intro hs; cases hs) $$ Hnc Hau with ⟨Hnc, HQ⟩
    unfold cleanQ
    icases HQ with ⟨Hu, -⟩
    iapply hfin h' (fun b hb hbn _ => hcur' b hb hbn) $$ Hnc Hp Hcp Hf Hcl Hsf Hu HA
  · unfold cleanQ
    icases HQ with ⟨Hu, -⟩
    unfold renDirOutA
    rcases o with _ | ⟨x, st⟩
    · simp only [logOut, claimOut]
      icases HA with ⟨-, -, HA⟩
      iapply hfin h' (fun b hb hbn _ => hcur' b hb hbn) $$ Hnc Hp Hcp Hf Hcl Hsf Hu HA
    · simp only [logOut, claimOut]
      icases HA with ⟨-, -, HA⟩
      iapply hfin _ (fun b hb hbn hbb => by
        simp only [NamesH.log]
        have hbk : b ≠ brokenName nm ts := fun e => hbb (e ▸ hbB)
        rw [restrictN_lookup _ _ _ hb, GMap.lookup_insert_ne _ _ (Ne.symm hbk),
          GMap.lookup_delete_ne _ (Ne.symm hbn)]
        exact hcur' b hb hbn) $$ Hnc Hp Hcp Hf Hcl Hsf Hu HA

/-- **`walAreaRes` back after the cleanup's rename** (see the file header): `nm.tmp`'s claim (absent)
merged back. -/
theorem create_cleanBack (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r nm : GoString)
    (N : NameSet) (h : NamesH) (cl : List (GoString × Claim)) (Wn : List GoString) (ht : NamesH)
    (hok : AreaOk N h cl Wn) (hnm : walNameOk nm) (hself : h.restrict jr N = h)
    (hft : ht.cur !! tmpName nm = none) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗ osSharedInv (L := hG.goose_localGS) R -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ createAreaL (W := W) jr nm N h cl Wn -∗
      osNames (L := hG.goose_localGS) jr (.only [tmpName nm]) (DFrac.own 1) ht ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ walAreaRes (L := hG.goose_localGS) jr := by
  iintro #Hinv #Hsi Hnc HaL HT
  unfold createAreaL
  icases HaL with ⟨Hu, %h', HN, Hcl, Hsf, %hh'⟩
  obtain ⟨b1, hb1, hb1L⟩ := walName_fresh Wn
  have hb1N : N.Mem b1 := (hok.1 b1 hb1).resolve_right hb1L
  have hb1t : b1 ≠ tmpName nm := fun he => tmpName_not_walName nm (he ▸ hb1)
  have hN1 : (N.diff [tmpName nm]).Mem b1 := (NameSet.mem_diff _ _ _).2 ⟨hb1N, by simpa using hb1t⟩
  have hNt := areaOk_tmp hok hnm
  imod walInv_mergeIn C Mr R jr r (N.diff [tmpName nm]) (.only [tmpName nm]) N
    _ ht b1 (tmpName nm) (walUnlockedTokX (W := W)) walUnlockedTokX_exclX ⊤ CoPset.subseteq_top
    walN_osShN_top hb1 hN1 (by simp [NameSet.Mem])
    (fun b hb => by simp only [NameSet.Mem, List.mem_singleton] at hb; subst hb; exact tmpName_not_walName nm)
    (fun b => by
      rw [NameSet.mem_diff]
      have e1 : (NameSet.only [tmpName nm]).Mem b ↔ b = tmpName nm := by simp [NameSet.Mem]
      rw [e1]
      by_cases hb : b = tmpName nm
      · subst hb; exact ⟨fun _ => Or.inr rfl, fun _ => hNt⟩
      · simp only [List.mem_singleton, hb, not_false_eq_true, and_true, or_false])
    $$ Hinv Hsi Hnc Hu HN HT with ⟨Hnc, -, %h3, HN, %hm⟩
  imod osNames_self R jr N _ h3 CoPset.subseteq_top $$ Hsi HN with ⟨HN, %hself3⟩
  have htc : h3.cur !! tmpName nm = none := by
    rw [cur_of_part hm.2.1 (by simp [NameSet.Mem] : (NameSet.only [tmpName nm]).Mem (tmpName nm)), hft]
  imodintro
  iframe Hnc
  iapply area_give N N h h3 cl jr (tmpName nm) Wn hok (fun _ => Iff.rfl) (tmpName_not_walName nm)
    (fun b hb hw hbb => by
      by_cases hbN : N.Mem b
      · have hbT : (N.diff [tmpName nm]).Mem b := (NameSet.mem_diff _ _ _).2 ⟨hbN, by simpa using hb⟩
        rw [cur_of_part hm.1 hbT]
        exact hh' b hbT (fun e => hw (e ▸ hnm)) hbb
      · rw [← hself3, ← hself]
        simp only [NamesH.restrict]
        rw [restrictN_lookup_not _ _ _ hbN, restrictN_lookup_not _ _ _ hbN])
  iframe HN Hcl Hsf
  rw [htc]
  iapply tmpCls_none

end iris

end WalFs
end EtcdGrove
end Perennial

end
