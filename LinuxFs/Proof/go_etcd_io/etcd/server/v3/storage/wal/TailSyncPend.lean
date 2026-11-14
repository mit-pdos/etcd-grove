/- Lean-first (no Rocq counterpart).

# The fdatasync of a lent tail after `ZeroToEnd`: the invariant's update (I3b, `wal-tc20`)

`ReadAll` registers its tail pending (`walPendTok`); `ZeroToEnd`'s first step turns the token into the
lent one (kind `false`: F-Z, or `TailPend`, `walLentRes_pendStop`); its fdatasync gives the key back
(`walLentRes_unpend`) once the synced layout has F-Z. The design of the W1 log's twenty-ninth session:

* `syncLay_anyP` (pure): `syncLay_any` from `TailZeros lay ∨ TailPend lay` and the handle's zeros from
  `wr` on (`WinZero lay g0`, `ZeroToEnd`'s post): an exact pending tail has F-Z (`tailZeros_of_pendEx`:
  its bytes past `wr = z0` are `old`'s, `ByteOk.val_unw`); a window's synced layout has F-Z from `TailZ0`
  (`tailZeros_syncW0`).
* `walTailsRes_cutP`: `walTailsRes_cut` over the lent token, the key out on success (`walLentRes_unpend`),
  everything back on failure.
* `walInvBody_syncP`: `walInvBody_sync` with the lent token.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailSync

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **An exact pending tail whose bytes from `wr` on are zero-valued has F-Z**: past `wr = z0` its bytes
are `old`'s (unwritten, `ByteOk.val_unw`). -/
theorem tailZeros_of_pendEx {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {g0 : SegG}
    (h : TailLast C Mr d lay g0) (hp : TailPend lay) (hwz : WinZero lay g0) : TailZeros lay := by
  obtain ⟨h1, -, h3, -, h5, -⟩ := h
  have hp1 := hp.1
  intro b hb1 hb2
  have hbl : b < g0.bs.length := by omega
  have hx : g0.bs[b]? = some (g0.bs[b]'hbl) := List.getElem?_eq_getElem hbl
  have hw : decide (b < lay.wr) = false := by simp; omega
  have hs : decide (b < lay.so) = false := by simp; omega
  have hB := h5 b _ hx
  rw [hw, hs] at hB
  rw [← hB.val_unw]; exact hwz b _ (by omega) hx

/-- **The layout after the fdatasync of a lent tail** (`syncLay_any` from F-Z or `TailPend`, and the
handle's zeros from `wr` on; see the file header). -/
theorem syncLay_anyP {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K : GMap GoString (Ino × List GoString)} {dir : GoString}
    {d : WalDur} {lay : WalLay} {ents : Ents} {pre : List SegG} {g0 : SegG}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0])
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length)
    (hZ : TailZeros lay ∨ TailPend lay) (hwz : WinZero lay g0)
    (hzf : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z) (hK : DirKeysOk C Mr jr s Ls cl n K none)
    (habs : WalAbsD C Mr d lay ents) :
    ∃ L : WalLay, L.segs = pre ++ [syncTail g0] ∧ L.j = lay.j ∧ L.nm = lay.nm ∧
      L.cuts = lay.cuts ∧ L.wr = lay.wr ∧ TailZeros L ∧
      TailBound C Mr { d with m := d.H.length } L ∧
      WalsOk C Mr R jr (walSyncS s dir d) (<[dir := L]> Ls) cl n ∧
      DirKeysOk C Mr jr (walSyncS s dir d) (<[dir := L]> Ls) cl n K none := by
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  by_cases hex : SegExact g0
  · have hZ' : TailZeros lay := hZ.elim id fun hp => tailZeros_of_pendEx ((habs.last g0 hg0).1 hex) hp hwz
    exact syncLay_any hC hW hd hl hs htail hZ' hzf hK habs
  · have hok : CrashOk C Mr d lay cl n :=
      (crashOkA_none_iff _ _ _ _ _ _).1 (hK.2.1 dir d lay hd hl (by simp))
    have hZ0 : TailZ0 lay := hZ.elim TailZ0.of_zeros TailZ0.of_pend
    exact ⟨syncLayW lay pre g0, rfl, rfl, rfl, rfl, rfl, tailZeros_syncW0 hZ0,
      tailBound_syncW habs hs htail,
      walsOk_syncW hC hW hd hl hs htail hZ0 hzf hex hwz hok,
      dirKeysOk_syncW hC hW hd hl hs htail hZ0 hzf hex hwz hK⟩

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The tail record of `dir`, its other half, by the lent token** (`walTailsRes_cut` for a lent tail of
kind `false`): the WAL, layout and last segment it records, F-Z or `TailPend` (`walLentRes_lookup`);
given a layout with F-Z whose record is the same (`tailG … = tg`), the token turns into the key
(`walLentRes_unpend`) and the layout of `dir` is replaced; or everything back as it was. -/
theorem walTailsRes_cutP (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState) (Ls : GMap GoString WalLay)
    (F : GMap Ino SegFl) (dir : GoString) (γ : GName) (k : Nat) (tg : TailG) :
    ⊢ walTailsRes (W := W) C Mr s Ls F -∗ walLentTokB (W := W) dir γ k false -∗ tailVar (W := W) γ tg -∗
      ∃ (d : WalDur) (lay : WalLay) (g0 : SegG),
        ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g0 ∧
          tg = tailG d lay g0.ino (F !! g0.ino) ∧ (TailZeros lay ∨ TailPend lay)⌝ ∗
        tailVar (W := W) γ tg ∗
        ((∀ (lay' : WalLay) (g : SegG) (F' : GMap Ino SegFl),
          ⌜lay'.segs.getLast? = some g ∧ TailZeros lay' ∧ TailBound C Mr d lay' ∧
            (∀ k la, k ≠ dir → Ls !! k = some la → ∀ g' ∈ la.segs, F' !! g'.ino = F !! g'.ino) ∧
            (∀ i, F' !! i ≠ none → i = g.ino ∨ (F !! i ≠ none ∧ i ≠ g0.ino)) ∧
            tailG d lay' g.ino (F' !! g.ino) = tg⌝ ==∗
          walTailKey (W := W) dir γ ∗ walTailsRes (W := W) C Mr s (<[dir := lay']> Ls) F') ∧
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
    imod walLentRes_unpend T Ls dir γ k false $$ Hk HL with ⟨Hk, HL⟩
    ispecialize HL $$ %lay' %hZ
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
      exact ⟨hd, GMap.lookup_insert _ _ _, hg', Or.inl hZ, hB'⟩
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

/-- **The fdatasync of a lent tail on the invariant** (`walInvBody_sync` by the lent token of kind
`false`): on success, given also the handle's zeros from `wr` on (`WinZero`), the invariant at the synced
state, the layout `syncLay_anyP`'s (F-Z), and the key out (`walTailsRes_cutP`); on failure everything
back, the token out. -/
theorem walInvBody_syncP (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (r : GoString) (s : AbsDiskState) (dir : GoString) (γ : GName) (k : Nat) (tg : TailG) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walLentTokB (W := W) dir γ k false -∗
      tailVar (W := W) γ tg -∗ walCutFrag (W := W) none -∗
      ∃ (F : GMap Ino SegFl) (d : WalDur) (lay : WalLay) (pre : List SegG) (g0 : SegG),
        ⌜s.wal !! dir = some d ∧ lay.segs = pre ++ [g0] ∧ tg = tailG d lay g0.ino (F !! g0.ino) ∧
          (∃ ents, WalAbsD C Mr d lay ents)⌝ ∗
        segResF (L := L) F g0 ∗ tailVar (W := W) γ tg ∗ walCutFrag (W := W) none ∗
        ((⌜F !! g0.ino = none ∧ lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length ∧
            (∀ z, g0.om.zf = some z → g0.bs.length ≤ z) ∧ WinZero lay g0⌝ -∗
          segRes (L := L) (syncTail g0) ==∗
          walInvBody (L := L) (W := W) C Mr R jr r (walSyncS s dir d) ∗
            walPast (W := W) (walSyncS s dir d) ∗ walTailKey (W := W) dir γ) ∧
        (segResF (L := L) F g0 -∗
          walInvBody (L := L) (W := W) C Mr R jr r s ∗ walLentTokB (W := W) dir γ k false)) := by
  letI := walAllG (W := W)
  iintro Hb Hk Hv Hcf
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hn, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  icases walCut_agree cp none $$ Hcp Hcf with %Hcpe
  subst Hcpe
  icases walTailsRes_cutP C Mr s Ls F dir γ k tg $$ Htl Hk Hv with
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
  iintro ⟨%hF, %htail, %hzf, %hwz⟩ Hseg
  icases Htlc with ⟨Htlc, -⟩
  have hmH : d.m ≤ d.H.length := habs.synced.1
  -- the synced layout: `syncLay`, or `syncLayW` in a resize window; F-Z either way
  obtain ⟨Lw, hLs, hLj, hLnm, hLc, hLw, hLZ, hLB, hLW, hLK⟩ :=
    syncLay_anyP hC HW hd hl hs htail hZP hwz hzf Hdko habs
  have e : tailG d Lw (syncTail g0).ino (F !! (syncTail g0).ino) = tg := by
    rw [htg]; unfold tailG; rw [hLc, hLw]; rfl
  imod Htlc $$ %Lw %(syncTail g0) %F [] with ⟨Hk, Htlc⟩
  · ipureintro
    exact ⟨by rw [hLs]; simp, hLZ,
      TailBound.congr (d := { d with m := d.H.length }) rfl rfl hLB,
      fun _ _ _ _ _ _ => rfl, fun i hi => if e : i = g0.ino then Or.inl e else Or.inr ⟨hi, e⟩, e⟩
  -- the ghost state at the synced state
  unfold walGhost
  icases Hg with ⟨⟨%G0, HGs, %HG0⟩, HP, Hh, %Hk0⟩
  ihave HP := absPast_grow _ s (walSyncS s dir d) (absLe_sync hd hmH) $$ HP
  imod absPast_snap _ (walSyncS s dir d) $$ HP with ⟨HP, Hpast⟩
  imodintro
  iframe Hk
  isplitr [Hpast]
  · iexists (<[dir := Lw]> Ls), cl, n, F
    iframe Hcl Hn HCR
    isplitl [HGs HP Hh]
    · iframe HP Hh
      isplitl [HGs]
      · iexists G0; iframe HGs; ipureintro; exact walMapLe_sync hd hmH HG0
      · ipureintro; exact walKeysInArea_sync hd Hk0
    isplitr
    · ipureintro; exact Har
    isplitl [Hpre Hseg Hrest]
    · iapply (laysResF_map (L := L) F _).2
      iapply (BigSepM.bigSepM_insert_delete (Φ := fun (_ : GoString) (lay : WalLay) =>
        iprop([∗list] g ∈ lay.segs, segResF (L := L) F g))).2
      isplitl [Hpre Hseg]
      · rw [hLs]
        iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
        iframe Hpre
        iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
        unfold segResF
        rw [show F !! (syncTail g0).ino = none from hF]
        iexact Hseg
      · iapply (laysResF_map (L := L) F _).1 $$ Hrest
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
      exact walsNamed_relay hl hs hLs hLj rfl rfl HNm
    isplitl [Hpk]
    · iapply walParked_relay Ls cl dir lay Lw pre g0 (syncTail g0) hl hs hLs hLj
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
    · iapply walNamesRes_insert _ _ _ _ _ _ Lw hl hLnm hLj $$ Hnms
    ipureintro; exact walsBounded_insSame Hbd rfl hd rfl
  · unfold walPast; iexact Hpast

end iris

end WalFs
end EtcdGrove
end Perennial

end
