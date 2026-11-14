/- Lean-first (no Rocq counterpart).

# The tail's fdatasync: the invariant's update (W6 of `notes/wal-fsext-plan.md`, "W6 implementation log")

`walInvBody_sync`: with the handle's key to its tail record, its half of the record and the lock
token's pending-cut flag (`walCutFrag none`: no cut's rename pending, so the WAL's crash condition has
no alternative layout), the invariant's contents give the WAL `d` of `dir`, its layout (the segments
`pre` then the tail `g0`) and the tail's part; given back, once every record is flushed (`wr` the
stream's end), no write in flight and the tail synced (`segRes (syncTail g0)`, the step's outcome), at
the WAL state `walSyncS s dir d` (the mark at the whole history) with the layout `syncLay lay pre g0`,
and that state's fact (`walPast`, for `walSyncedLb`). The tail record is unchanged (`syncLay` keeps the
cuts and the write position). The pure part is `TailSyncPure.lean`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailSyncPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutAuLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- The program's map stays below the WAL state across a sync. -/
theorem walMapLe_sync {G : GMap GoString WalDur} {s : AbsDiskState} {dir : GoString} {d : WalDur}
    (hd : s.wal !! dir = some d) (hm : d.m ≤ d.H.length) (h : walMapLe G s.wal) :
    walMapLe G (walSyncS s dir d).wal := by
  intro k
  by_cases e : k = dir
  · subst e
    rw [walSyncS_lookup]
    have h1 := h k
    rw [hd] at h1
    cases hg : G !! k with
    | none => rw [hg] at h1; exact h1.elim
    | some d0 =>
      rw [hg] at h1
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h1
      exact ⟨a1, a2, a3, a4, a5, a6, Nat.le_trans a7 hm, a8⟩
  · rw [walSyncS_lookup_ne s dir d e]; exact h k

theorem absLe_sync {s : AbsDiskState} {dir : GoString} {d : WalDur} (hd : s.wal !! dir = some d)
    (hm : d.m ≤ d.H.length) : absLe s (walSyncS s dir d) := by
  refine ⟨rfl, fun _ h => h, fun k d1 hk => ?_⟩
  by_cases e : k = dir
  · subst e
    rw [hd] at hk; cases hk
    exact ⟨_, walSyncS_lookup s k d, hm, Nat.le_refl _, id⟩
  · exact ⟨d1, by rw [walSyncS_lookup_ne s dir d e]; exact hk, Nat.le_refl _, Nat.le_refl _, id⟩

theorem walKeysInArea_sync {s : AbsDiskState} {dir : GoString} {d : WalDur}
    (hd : s.wal !! dir = some d) (h : walKeysInArea s) : walKeysInArea (walSyncS s dir d) := by
  intro k d1 hk
  by_cases e : k = dir
  · subst e; exact h k d hd
  · rw [walSyncS_lookup_ne s dir d e] at hk; exact h k d1 hk

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **A resource per segment, with a layout replaced** by one whose segments are the old ones with
the last replaced (`Φ g0 ⊢ Φ g`). -/
theorem segsAll_sep_relay (Φ : SegG → IProp GF) (Ls : GMap GoString WalLay) (dir : GoString)
    (lay lay' : WalLay) (pre : List SegG) (g0 g : SegG) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (hs' : lay'.segs = pre ++ [g]) (hΦ : Φ g0 ⊢ Φ g) :
    ([∗list] x ∈ segsAll Ls, Φ x) ⊢ [∗list] x ∈ segsAll (<[dir := lay']> Ls), Φ x := by
  refine (segsAll_sep_map Φ Ls).1.trans ?_
  refine (BigSepM.bigSepM_delete (Φ := fun (_ : GoString) (lay : WalLay) =>
    iprop([∗list] x ∈ lay.segs, Φ x)) hl).1.trans ?_
  refine Entails.trans ?_ (segsAll_sep_map Φ _).2
  refine Entails.trans ?_ (BigSepM.bigSepM_insert_delete (Φ := fun (_ : GoString) (lay : WalLay) =>
    iprop([∗list] x ∈ lay.segs, Φ x))).2
  refine sep_mono ?_ .rfl
  rw [hs, hs']
  refine (BigSepL.bigSepL_append (PROP := IProp GF)).1.trans ?_
  refine Entails.trans ?_ (BigSepL.bigSepL_append (PROP := IProp GF)).2
  refine sep_mono .rfl ?_
  refine (BigSepL.bigSepL_singleton (PROP := IProp GF) (Φ := fun _ x => Φ x)).1.trans ?_
  exact hΦ.trans (BigSepL.bigSepL_singleton (PROP := IProp GF) (Φ := fun _ x => Φ x)).2

/-- **The parked halves with a layout replaced** by one of the same directory, its last segment
replaced by one of the same inode and length. -/
theorem walParked_relay (Ls : GMap GoString WalLay) (cl : List Claim) (dir : GoString)
    (lay lay' : WalLay) (pre : List SegG) (g0 g : SegG) {F : GMap Ino SegFl} (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (hs' : lay'.segs = pre ++ [g]) (hj : lay'.j = lay.j)
    (hino : g.ino = g0.ino) (hlen : g.bs.length = g0.bs.length) :
    walParked (L := L) (W := W) Ls cl F ⊢ walParked (L := L) (W := W) (<[dir := lay']> Ls) cl F := by
  unfold walParked
  iintro ⟨%b, %o, Ha, Hoa, %hb, Hs, Hc, Ht⟩
  iexists b, o
  iframe Ha Hoa
  isplitr
  · ipureintro; exact hb
  isplitl [Hs]
  · iapply segsAll_sep_relay (fun x => iprop(if x.ino ∈ o.O then emp else segResP (L := L) x)) Ls dir
      lay lay' pre g0 g hl hs hs' ?_ $$ Hs
    rw [hino]
    split
    · exact .rfl
    · unfold segResP
      rw [hino, hlen]
  isplitl [Hc]
  · iapply BigSepL.bigSepL_mono (fun {k c} _ => ?_) $$ Hc
    have e : ParkedClaim (<[dir := lay']> Ls) o.D c ↔ ParkedClaim Ls o.D c := by
      unfold ParkedClaim; rw [walDirClaimOf_insert hl hj c]
    simp only [propext e]
    exact .rfl
  · iapply walTmpParked_insert Ls o.T dir lay lay' hl hj $$ Ht

/-- **F-Z of the WAL in `dir`**, from its tail record (the handle's key and half). -/
theorem walTailsRes_zeros (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState)
    (Ls : GMap GoString WalLay) (F : GMap Ino SegFl) (dir : GoString) (γ : GName) (tg : TailG) :
    ⊢ walTailsRes (W := W) C Mr s Ls F -∗ walTailKey (W := W) dir γ -∗
      ⌜∀ d lay, s.wal !! dir = some d → Ls !! dir = some lay → TailZeros lay ∧ TailBound C Mr d lay⌝ ∗
        walTailsRes (W := W) C Mr s Ls F ∗ walTailKey (W := W) dir γ := by
  letI := walAllG (W := W)
  unfold walTailsRes
  iintro ⟨%T, HTa, %HTo, HTm⟩ Hk
  icases walTailKey_lookup T dir γ $$ HTa Hk with %HT
  ihave ⟨Hent, HTm⟩ := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (γ : GName) =>
    iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZeros lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).1 $$ HTm
  icases Hent with ⟨%d, %lay, %g0, %hp, Hv'⟩
  isplitr
  · ipureintro
    intro d' lay' hd' hl'
    rw [hp.2.1] at hl'; cases hl'
    rw [hp.1] at hd'; cases hd'
    exact ⟨hp.2.2.2.1, hp.2.2.2.2⟩
  iframe Hk
  iexists T
  iframe HTa
  isplitr
  · ipureintro; exact HTo
  iapply (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (γ : GName) =>
    iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZeros lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).2
  iframe HTm
  iexists d, lay, g0
  iframe Hv'
  ipureintro; exact hp

/-- **The tail's fdatasync on the invariant** (see the file header). -/
theorem walInvBody_sync (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (r : GoString) (s : AbsDiskState) (dir : GoString) (γ : GName) (tg : TailG) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walTailKey (W := W) dir γ -∗
      tailVar (W := W) γ tg -∗ walCutFrag (W := W) none -∗
      ∃ (F : GMap Ino SegFl) (d : WalDur) (lay : WalLay) (pre : List SegG) (g0 : SegG),
        ⌜s.wal !! dir = some d ∧ lay.segs = pre ++ [g0] ∧ tg = tailG d lay g0.ino (F !! g0.ino) ∧
          (∃ ents, WalAbsD C Mr d lay ents)⌝ ∗
        segResF (L := L) F g0 ∗ walTailKey (W := W) dir γ ∗ tailVar (W := W) γ tg ∗
        walCutFrag (W := W) none ∗
        (⌜F !! g0.ino = none ∧ lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length ∧
            (∀ z, g0.om.zf = some z → g0.bs.length ≤ z) ∧ SegExact g0⌝ -∗
          segRes (L := L) (syncTail g0) ==∗
          walInvBody (L := L) (W := W) C Mr R jr r (walSyncS s dir d) ∗
            walPast (W := W) (walSyncS s dir d)) ∧
        (segResF (L := L) F g0 -∗ walInvBody (L := L) (W := W) C Mr R jr r s) := by
  letI := walAllG (W := W)
  iintro Hb Hk Hv Hcf
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hn, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt⟩
  icases walCut_agree cp none $$ Hcp Hcf with %Hcpe
  subst Hcpe
  icases walTailsRes_zeros C Mr s Ls F dir γ tg $$ Htl Hk with ⟨%HZs, Htl, Hk⟩
  icases walTailsRes_cut C Mr s Ls F dir γ tg $$ Htl Hk Hv with
    ⟨%d, %lay, %g0, %hp, Hk, Hv, Hv', Htlc⟩
  obtain ⟨hd, hl, hg, htg⟩ := hp
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
  iframe Hlast Hk Hv Hcf
  have hZB := HZs d lay hd hl
  isplit; rotate_left
  · -- the step failed: everything back as it was
    iintro Hlast
    have eL : <[dir := lay]> Ls = Ls := GMap.insert_id Ls dir lay hl
    iexists Ls, cl, n, F
    iframe Hg Hcl Hn HCR Hpk
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
    isplitl [Htlc Hv']
    · iapply (show walTailsRes (W := W) C Mr s (<[dir := lay]> Ls) F ⊢ walTailsRes (W := W) C Mr s Ls F by rw [eL])
      iapply Htlc $$ %lay %g0 %F [] [Hv']
      · ipureintro
        exact ⟨hg, hZB.1, hZB.2, fun _ _ _ _ _ _ => rfl, fun i hi =>
          if e : i = g0.ino then Or.inl e else Or.inr ⟨hi, e⟩⟩
      · rw [← htg]; iexact Hv'
    isplitr
    · ipureintro; exact Hab
    isplitr
    · ipureintro; exact HNm
    isplitl [Hdk Hcp]
    · iexists K, none
      iframe Hdk Hcp
      ipureintro; exact Hdko
    ipureintro; exact HAt
  iintro ⟨%hF, %htail, %hzf, %hex⟩ Hseg
  -- F-Z, from the tail record's entry (kept by `walTailsRes_cut`'s premise)
  have hZ : TailZeros lay := hZB.1
  have hnd : (lay.segs.map (·.ino)).Nodup := ((segsAll_nodup_iff Ls).1 HW.2.2.1).1 dir lay hl
  have hmH : d.m ≤ d.H.length := habs.synced.1
  have hok : CrashOk C Mr d lay cl n :=
    (crashOkA_none_iff _ _ _ _ _ _).1 (Hdko.2.1 dir d lay hd hl (by simp))
  -- the ghost state at the synced state
  unfold walGhost
  icases Hg with ⟨⟨%G0, HGs, %HG0⟩, HP, Hh, %Hk0⟩
  ihave HP := absPast_grow _ s (walSyncS s dir d) (absLe_sync hd hmH) $$ HP
  imod absPast_snap _ (walSyncS s dir d) $$ HP with ⟨HP, Hpast⟩
  imodintro
  isplitr [Hpast]
  · iexists (<[dir := syncLay lay pre g0]> Ls), cl, n, F
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
      · simp only [syncLay]
        iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
        iframe Hpre
        iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
        unfold segResF
        rw [show F !! (syncTail g0).ino = none from hF]
        iexact Hseg
      · iapply (laysResF_map (L := L) F _).1 $$ Hrest
    isplitr
    · ipureintro; exact walsOk_sync hC HW hd hl hs htail hZ hzf hex hok
    isplitr
    · ipureintro; exact HWC
    isplitl [Htlc Hv']
    · have hmono : ∀ k d1, s.wal !! k = some d1 → ∃ d', (walSyncS s dir d).wal !! k = some d' ∧
          d'.H = d1.H ∧ d'.metadata = d1.metadata := by
        intro k d1 hk
        by_cases e : k = dir
        · subst e; rw [hd] at hk; cases hk
          exact ⟨_, walSyncS_lookup s k d, rfl, rfl⟩
        · exact ⟨d1, by rw [walSyncS_lookup_ne s dir d e]; exact hk, rfl, rfl⟩
      iapply walTailsRes_mono C Mr s (walSyncS s dir d) _ F hmono
      iapply Htlc $$ %(syncLay lay pre g0) %(syncTail g0) %F [] [Hv']
      · ipureintro
        exact ⟨by simp [syncLay], hZ,
          TailBound.congr (d := { d with m := d.H.length }) rfl rfl (tailBound_sync habs hs htail),
          fun _ _ _ _ _ _ => rfl, fun i hi => if e : i = g0.ino then Or.inl e else Or.inr ⟨hi, e⟩⟩
      · have e : tailG d (syncLay lay pre g0) (syncTail g0).ino (F !! (syncTail g0).ino) = tg := by
          rw [htg]; rfl
        rw [e]; iexact Hv'
    isplitr
    · ipureintro; exact ⟨absentNone_sync Hab.1, dirsAvoid_sync Hab.2⟩
    isplitr
    · ipureintro
      exact walsNamed_relay hl hs rfl rfl rfl rfl HNm
    isplitl [Hpk]
    · iapply walParked_relay Ls cl dir lay (syncLay lay pre g0) pre g0 (syncTail g0) hl hs rfl rfl
        rfl (by simp [syncTail]) $$ Hpk
    isplitl [Hdk Hcp]
    · iexists K, none
      iframe Hdk Hcp
      ipureintro
      exact dirKeysOk_sync hC HW hd hl hs htail hZ hzf hex Hdko
    ipureintro
    exact walsAt_insert hl rfl rfl HAt
  · unfold walPast; iexact Hpast

end iris

end WalFs
end EtcdGrove
end Perennial

end
