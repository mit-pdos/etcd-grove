/- Lean-first (no Rocq counterpart).

# The fdatasync of a lent tail `ZeroToEnd` left partway: the invariant's update (unit `synclent`)

`Close` of a failed `ReadAll`'s handle (`WAL.Close.spec` (state `failed`)) syncs the tail `ZeroToEnd` left
(`walTailPE`, `WAL.sync.specLentE`): lent by the token of kind `false`, its bytes from `wr` on a torn
frame's with a zero length word, a resize window maybe open. Its fdatasync keeps the tail lent, the
layout replaced by `syncLay_anyE`'s (F-Z or `TailPend`, `TailSyncLayP.lean`), and the token's recorded
`|old|` replaced by the new layout's (`walLentRes_relend`): `syncLayP`'s `old` is the synced tail's
length, and the token is not turned into the key (no F-Z). `Close` then puts the tail back by the token
(`walInv_untailLent`, over `walInvBody_untailL`).

* `walLentRes_relend`: a lent tail's layout replaced, F-Z or `TailPend`, the token's `|old|` with it;
* `walTailsRes_cutPE`: `walTailsRes_cutP` with the token kept (`walLentRes_relend`), F-Z or `TailPend`;
* `walInvBody_syncPE`: `walInvBody_syncP` from the reader's stop on the handle's values at `wr`
  (`PendStop`; until P6 item 2 the zero length word there) in place of its zeros from `wr` on, the token
  kept;
* `walInv_untailLent`: `walInv_untailPend` for a token of kind `false`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailSyncPend
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailSyncLayP
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.UnregLent
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSteps

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

/-- **A lent tail's layout replaced, F-Z or `TailPend`, the token's `|old|` with it** (the fdatasync of a
tail `ZeroToEnd` left partway: `syncLayP` changes `old`'s length). -/
theorem walLentRes_relend (T : GMap GoString GName) (Ls : GMap GoString WalLay) (dir : GoString)
    (γ : GName) (k : Nat) (lay' : WalLay) (hz : TailZeros lay' ∨ TailPend lay') :
    ⊢ walLentTokB (W := W) dir γ k false -∗ walLentRes (W := W) T Ls ==∗
      walLentTokB (W := W) dir γ lay'.old.length false ∗ walLentRes (W := W) T (<[dir := lay']> Ls) := by
  unfold walLentRes
  iintro Hl ⟨%M, Ha, %HZ, %HI, Hm⟩
  icases walLentTok_lookup M dir γ k false $$ Ha Hl with %hM
  ihave ⟨⟨%hx, Hk⟩, Hm⟩ := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (x : GName × Nat × Bool) =>
    iprop(⌜LentOk T Ls dir x⌝ ∗ walTailKey (W := W) dir x.1)) hM).1 $$ Hm
  imod walLentTok_delete M dir γ k false $$ Ha Hl with Ha
  have hM0 : (GMap.delete dir M) !! dir = none := GMap.lookup_delete_eq _ _
  imod walLentTok_insert (GMap.delete dir M) dir γ lay'.old.length false hM0 $$ Ha with ⟨Ha, Hl⟩
  imodintro
  iframe Hl
  iexists _
  iframe Ha
  isplitr
  · ipureintro
    intro d la hT hla hnp
    by_cases e : d = dir
    · subst e; rw [GMap.lookup_insert] at hla; cases hla
      rcases hz with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by rw [GMap.lookup_insert]; simp, h⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hla
      have e1 : (<[dir := (γ, lay'.old.length, false)]> (GMap.delete dir M)) !! d = M !! d := by
        rw [GMap.lookup_insert_ne _ _ (Ne.symm e), GMap.lookup_delete_ne _ (Ne.symm e)]
      exact zerosOr_congr e1 (HZ d la hT hla (fun x hx => hnp x (by rw [e1]; exact hx)))
  isplitr
  · ipureintro; exact HI.insert (hz.elim TailZ0.of_zeros TailZ0.of_pend)
  iapply (BigSepM.bigSepM_insert (Φ := fun (d : GoString) (x : GName × Nat × Bool) =>
    iprop(⌜LentOk T (<[dir := lay']> Ls) d x⌝ ∗ walTailKey (W := W) d x.1)) hM0).2
  isplitl [Hk]
  · iframe Hk
    ipureintro; exact ⟨hx.1, lay', GMap.lookup_insert _ _ _, rfl, fun h => by cases h⟩
  iapply BigSepM.bigSepM_mono (fun {k' x} hk => ?_) $$ Hm
  iintro ⟨%hx', Hk⟩
  iframe Hk
  ipureintro
  have e : k' ≠ dir := by
    change GMap.delete dir M !! k' = some x at hk; rintro rfl; rw [GMap.lookup_delete_eq] at hk; cases hk
  obtain ⟨hT, la, hla, hlen⟩ := hx'
  exact ⟨hT, la, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hla, hlen⟩

/-- **The tail record of `dir`, its other half, by the lent token, the token kept** (`walTailsRes_cutP`
with `walLentRes_relend`: the new layout F-Z or `TailPend`). -/
theorem walTailsRes_cutPE (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState) (Ls : GMap GoString WalLay)
    (F : GMap Ino SegFl) (dir : GoString) (γ : GName) (k : Nat) (tg : TailG) :
    ⊢ walTailsRes (W := W) C Mr s Ls F -∗ walLentTokB (W := W) dir γ k false -∗ tailVar (W := W) γ tg -∗
      ∃ (d : WalDur) (lay : WalLay) (g0 : SegG),
        ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g0 ∧
          tg = tailG d lay g0.ino (F !! g0.ino) ∧ (TailZeros lay ∨ TailPend lay)⌝ ∗
        tailVar (W := W) γ tg ∗
        ((∀ (lay' : WalLay) (g : SegG) (F' : GMap Ino SegFl),
          ⌜lay'.segs.getLast? = some g ∧ (TailZeros lay' ∨ TailPend lay') ∧ TailBound C Mr d lay' ∧
            (∀ k la, k ≠ dir → Ls !! k = some la → ∀ g' ∈ la.segs, F' !! g'.ino = F !! g'.ino) ∧
            (∀ i, F' !! i ≠ none → i = g.ino ∨ (F !! i ≠ none ∧ i ≠ g0.ino)) ∧
            tailG d lay' g.ino (F' !! g.ino) = tg⌝ ==∗
          walLentTokB (W := W) dir γ lay'.old.length false ∗
            walTailsRes (W := W) C Mr s (<[dir := lay']> Ls) F') ∧
         (walTailsRes (W := W) C Mr s Ls F ∗ walLentTokB (W := W) dir γ k false)) := by
  letI := walAllG (W := W)
  unfold walTailsRes tailVar
  iintro ⟨%T, HTa, %HTo, %HTi, HTm, HL⟩ Hk Hv
  icases walLentRes_lookup T Ls dir γ k false $$ Hk HL with ⟨%hx, Hk, HL⟩
  have HT : T !! dir = some γ := hx.1.1
  ihave ⟨Hent, HTm⟩ := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (γ : GName) =>
    iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZ0 lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).1 $$ HTm
  icases Hent with ⟨%d, %lay, %g0, %hp, Hv'⟩
  obtain ⟨hd, hl, hg, hz0, hB⟩ := hp
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Htg
  iexists d, lay, g0
  isplitr
  · ipureintro; exact ⟨hd, hl, hg, Htg, hx.2 rfl lay hl⟩
  iframe Hv
  isplit
  · iintro %lay' %g %F' %hp'
    obtain ⟨hg', hZ, hB', hF, hFo, he⟩ := hp'
    imod walLentRes_relend T Ls dir γ k lay' hZ $$ Hk HL with ⟨Hk, HL⟩
    imodintro
    iframe Hk
    iexists T
    iframe HTa HL
    isplitr
    · ipureintro; exact HTo.insert HT hl hg hg' hFo
    isplitr
    · ipureintro
      exact HTi.of_reg dir (fun h => by rw [HT] at h; cases h) (fun _ _ => rfl)
        (fun k hk => GMap.lookup_insert_ne _ _ (Ne.symm hk))
    iapply (BigSepM.bigSepM_delete (Φ := fun (k : GoString) (γ' : GName) =>
      iprop(∃ (d' : WalDur) (la : WalLay) (g' : SegG),
        ⌜s.wal !! k = some d' ∧ (<[dir := lay']> Ls) !! k = some la ∧
          la.segs.getLast? = some g' ∧ TailZ0 la ∧ TailBound C Mr d' la⌝ ∗
        ghostVar γ' (1 : Qp).half (tailG d' la g'.ino (F' !! g'.ino)))) HT).2
    isplitl [Hv']
    · iexists d, lay', g
      rw [he, Htg]
      iframe Hv'
      ipureintro
      exact ⟨hd, GMap.lookup_insert _ _ _, hg', hZ.elim TailZ0.of_zeros TailZ0.of_pend, hB'⟩
    · iapply BigSepM.bigSepM_mono (fun {k γ'} hk => ?_) $$ HTm
      have hne : k ≠ dir := by
        change GMap.delete dir T !! k = some γ' at hk
        rintro rfl; rw [GMap.lookup_delete_eq] at hk; cases hk
      iintro ⟨%d', %lay1, %g', %hp', Hv''⟩
      obtain ⟨hd', hl', hg1, hZ', hB''⟩ := hp'
      have he' : F' !! g'.ino = F !! g'.ino := hF k lay1 hne hl' g' (List.mem_of_getLast? hg1)
      iexists d', lay1, g'
      rw [he']
      iframe Hv''
      ipureintro
      exact ⟨hd', by rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact hl', hg1, hZ', hB''⟩
  · iframe Hk
    iexists T
    iframe HTa HL
    isplitr
    · ipureintro; exact HTo
    isplitr
    · ipureintro; exact HTi
    iapply (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (γ : GName) =>
      iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
        ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZ0 lay ∧
          TailBound C Mr d lay⌝ ∗
        ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).2
    iframe HTm
    iexists d, lay, g0
    iframe Hv'
    ipureintro; exact ⟨hd, hl, hg, hz0, hB⟩

/-- **The fdatasync of a lent tail `ZeroToEnd` left partway on the invariant** (`walInvBody_syncP` from the
handle's zero length word at `wr`, the token kept; see the file header). -/
theorem walInvBody_syncPE (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (r : GoString) (s : AbsDiskState) (dir : GoString) (γ : GName) (k : Nat) (tg : TailG) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walLentTokB (W := W) dir γ k false -∗
      tailVar (W := W) γ tg -∗ walCutFrag (W := W) none -∗
      ∃ (F : GMap Ino SegFl) (d : WalDur) (lay : WalLay) (pre : List SegG) (g0 : SegG),
        ⌜s.wal !! dir = some d ∧ lay.segs = pre ++ [g0] ∧ tg = tailG d lay g0.ino (F !! g0.ino) ∧
          (∃ ents, WalAbsD C Mr d lay ents)⌝ ∗
        segResF (L := L) F g0 ∗ tailVar (W := W) γ tg ∗ walCutFrag (W := W) none ∗
        ((⌜F !! g0.ino = none ∧ lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length ∧
            (∀ z, g0.om.zf = some z → g0.bs.length ≤ z) ∧
            PendStop C Mr (g0.bs.map (·.1)) lay.wr
              (WalEnc.chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts)))⌝ -∗
          segRes (L := L) (syncTail g0) ==∗
          walInvBody (L := L) (W := W) C Mr R jr r (walSyncS s dir d) ∗
            walPast (W := W) (walSyncS s dir d) ∗ ∃ k' : Nat, walLentTokB (W := W) dir γ k' false) ∧
        (segResF (L := L) F g0 -∗
          walInvBody (L := L) (W := W) C Mr R jr r s ∗ walLentTokB (W := W) dir γ k false)) := by
  letI := walAllG (W := W)
  iintro Hb Hk Hv Hcf
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hn, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  icases walCut_agree cp none $$ Hcp Hcf with %Hcpe
  subst Hcpe
  icases walTailsRes_cutPE C Mr s Ls F dir γ k tg $$ Htl Hk Hv with
    ⟨%d, %lay, %g0, %hp, Hv, Htlc⟩
  obtain ⟨hd, hl, hg, htg, hZP⟩ := hp
  obtain ⟨pre, hs⟩ := List.getLast?_eq_some_iff.1 hg
  obtain ⟨lay1, nm, hj, hl1, hA, hjr, hnm, hc, habs, hcr⟩ := HW.1 dir d hd
  rw [hl] at hl1; cases hl1
  icases (laysResF_del (L := L) F Ls dir lay hl).1 $$ Hlays with ⟨Hsegs, Hrest⟩
  rw [hs]
  icases (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ Hsegs with ⟨Hpre, Hlast⟩
  icases (BigSepL.bigSepL_singleton (PROP := IProp GF)).1 $$ Hlast with Hlast
  iexists F, d, lay, pre, g0
  isplitr
  · ipureintro; exact ⟨hd, hs, htg, ⟨_, habs⟩⟩
  iframe Hlast Hv Hcf
  isplit; rotate_left
  · -- the step failed: everything back as it was
    iintro Hlast
    icases Htlc with ⟨-, ⟨Htl, Hk⟩⟩
    iframe Hk
    iexists Ls, cl, n, F
    iframe Hg Hcl Hn HCR Hpk Htl
    isplitr
    · ipureintro; exact Har
    isplitl [Hpre Hlast Hrest]
    · iapply (laysResF_del (L := L) F Ls dir lay hl).2
      iframe Hrest
      rw [hs]
      iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
      iframe Hpre
      iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
      iexact Hlast
    isplitr
    · ipureintro; exact HW
    isplitr
    · ipureintro; exact HWC
    isplitr
    · ipureintro; exact Hab
    isplitr
    · ipureintro; exact HNm
    isplitl [Hdk Hcp]
    · iexists K, none
      iframe Hdk Hcp
      ipureintro; exact Hdko
    iframe Hnms; ipureintro; exact ⟨HAt, Hbd⟩
  iintro ⟨%hF, %htail, %hzf, %hpv⟩ Hseg
  icases Htlc with ⟨Htlc, -⟩
  have hmH : d.m ≤ d.H.length := habs.synced.1
  -- the synced layout: `syncLay_any`'s (F-Z), or `syncLayP` (`TailPend`)
  obtain ⟨Lw, hLs, hLj, hLnm, hLc, hLw, hLpg, hLZ, hLB, hLW, hLK⟩ :=
    syncLay_anyE hC HW hd hl hs htail hZP hpv hzf Hdko habs
  have e : tailG d Lw (syncTail g0).ino (F !! (syncTail g0).ino) = tg := by
    rw [htg]; unfold tailG; rw [hLc, hLw]; rfl
  imod Htlc $$ %Lw %(syncTail g0) %F [] with ⟨Hk, Htlc⟩
  · ipureintro
    exact ⟨by rw [hLs]; simp, hLZ,
      TailBound.congr (d := { d with m := d.H.length }) rfl rfl hLB,
      fun _ _ _ _ _ _ => rfl, fun i hi => if e : i = g0.ino then Or.inl e else Or.inr ⟨hi, e⟩, e⟩
  -- the ghost state at the synced state
  unfold walGhost
  icases Hg with ⟨⟨%G0, HGs, %HG0⟩, HP, ⟨Hh0, Hlk⟩, %Hk0, #Hst⟩
  ihave Hh : iprop(walHandleAuth (W := W) ∗ walLksAuth (W := W) (walSyncS s dir d)) $$ [Hh0 Hlk]
  · iframe Hh0
    iapply walLksAuth_mono s (walSyncS s dir d)
      (unlMono_insert s dir _ (fun d' h => by rw [hd] at h; cases h; exact Nat.le_refl _)) $$ Hlk
  ihave HP := absPast_grow _ s (walSyncS s dir d) (absLe_sync hd hmH) $$ HP
  imod absPast_snap _ (walSyncS s dir d) $$ HP with ⟨HP, Hpast⟩
  imodintro
  isplitr [Hpast Hk]
  · iexists (<[dir := Lw]> Ls), cl, n, F
    iframe Hcl Hn HCR
    isplitl [HGs HP Hh]
    · iframe HP Hh
      isplitl [HGs]
      · iexists G0; iframe HGs; ipureintro; exact walMapLe_sync hd hmH HG0
      · isplitr
        · ipureintro; exact walKeysInArea_sync hd Hk0
        · iapply walStepsLb_mono _ _ (fun n hn => WalsStepped.insert (d' := { d with m := d.H.length }) hn rfl (hn dir d hd)) $$ Hst
    isplitr
    · ipureintro; exact Har
    isplitl [Hpre Hseg Hrest]
    · iapply laysResF_put (L := L) F Ls dir lay Lw hLpg
      iframe Hrest
      rw [hLs]
      iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
      iframe Hpre
      iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
      unfold segResF
      rw [show F !! (syncTail g0).ino = none from hF]
      iexact Hseg
    isplitr
    · ipureintro; exact hLW
    isplitr
    · ipureintro; exact HWC
    isplitl [Htlc]
    · have hmono : ∀ k d1, s.wal !! k = some d1 → ∃ d', (walSyncS s dir d).wal !! k = some d' ∧
          d'.H = d1.H ∧ d'.metadata = d1.metadata := by
        intro k d1 hk
        by_cases e : k = dir
        · subst e; rw [hd] at hk; cases hk
          exact ⟨_, walSyncS_lookup s k d, rfl, rfl⟩
        · exact ⟨d1, by rw [walSyncS_lookup_ne s dir d e]; exact hk, rfl, rfl⟩
      have hmono' : ∀ k d', (walSyncS s dir d).wal !! k = some d' → ∃ d1, s.wal !! k = some d1 ∧
          d'.H = d1.H ∧ d'.metadata = d1.metadata := by
        intro k d' hk
        by_cases e : k = dir
        · subst e; rw [walSyncS_lookup] at hk; cases hk
          exact ⟨d, hd, rfl, rfl⟩
        · exact ⟨d', by rw [walSyncS_lookup_ne s dir d e] at hk; exact hk, rfl, rfl⟩
      iapply walTailsRes_mono C Mr s (walSyncS s dir d) _ F hmono hmono' $$ Htlc
    isplitr
    · ipureintro; exact ⟨absentNone_sync Hab.1, dirsAvoid_sync Hab.2⟩
    isplitr
    · ipureintro
      exact walsNamed_relay hl hs hLs hLj rfl rfl hLpg HNm
    isplitl [Hpk]
    · iapply walParked_relay Ls cl dir lay Lw pre g0 (syncTail g0) hl hs hLs hLj hLpg
        rfl (by simp [syncTail]) $$ Hpk
    isplitl [Hdk Hcp]
    · iexists K, none
      iframe Hdk Hcp
      ipureintro
      exact hLK
    isplitr
    · ipureintro
      exact walsAt_insert hl hLnm hLj HAt
    isplitl [Hnms]
    · ihave Hnms := walNamesRes_congr R jr r Ls s (walSyncS s dir d)
        (namedSub_ins s dir d _ hd rfl) $$ Hnms
      iapply walNamesRes_insert _ _ _ _ _ _ Lw hl hLnm hLj $$ Hnms
    ipureintro; exact ⟨walsBounded_insSame Hbd.1 rfl hd rfl rfl, Hbd.2⟩
  · isplitl [Hpast]
    · unfold walPast; iexact Hpast
    · iexists _; iexact Hk


/-- **A lent tail (token of kind `false`) unregistered** (`walInv_untailPend`'s form; the put-back after
`WAL.sync.specLentE`'s fdatasync). -/
theorem walInv_untailLent [go.BasicIntoValInj] (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (wr : Nat) (ino : Ino) (m : OsMeta) (bs : List ByteG)
    (hTM : TailMetaR m bs ∧ (∀ z, m.zf = some z → m.size ≤ z) ∧ ∀ y ∈ bs, y = Fs.durB y.1)
    (hwr : wr = (tailStream Mr H md cuts).length) :
    ⊢ walInv (L := L) (W := W) walCodec Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walTailsFrag (W := W) (<[dir := γ]> ∅) -∗ walLentTokB (W := W) dir γ k false -∗
      tailVar (W := W) γ ((H, md, cuts, wr, ino, none) : TailG) -∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m -∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs
      ={⊤}=∗ notCrashed (hC := L.goose_crashGS) ∗ walTailsFrag (W := W) ∅ ∗
        osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs := by
  iintro #Hinv Hnc Htf Htk Hv Hm Hb
  iapply walInv_step walCodec Mr R jr r
    iprop(walTailsFrag (W := W) (<[dir := γ]> ∅) ∗ walLentTokB (W := W) dir γ k false ∗
      tailVar (W := W) γ ((H, md, cuts, wr, ino, none) : TailG) ∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs)
    iprop(walTailsFrag (W := W) ∅ ∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs)
    ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb ⟨Htf, Htk, Hv, Hm, Hbs⟩
      imod walInvBody_untailL Mr R jr r s dir γ γ k false H md cuts wr ino m bs hTM hwr
        $$ Hb Htf Htk Hv Hm Hbs with ⟨%d, -, Hb, Htf, Hm, Hbs⟩
      imodintro
      iframe)
    $$ Hinv Hnc [Htf Htk Hv Hm Hb]
  iframe

end iris

end WalFs
end EtcdGrove
end Perennial

end
