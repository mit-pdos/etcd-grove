/- Lean-first (no Rocq counterpart).

# A lent tail unregistered (B1 of the W4c U5 log, fifth session)

`Close` of the handle a failed `ReadAll` leaves (`WAL.Close.spec` (state `failed`)) puts back a tail the handle
holds by the lent token (`walLentTokB dir γ k p`: `p = true`, registered, not yet zeroed, the exits
before `ZeroToEnd`; `p = false`, after `ZeroToEnd`'s first step), not by the key. As
`walInvBody_untail` (`CloseLaw.lean`) over `TailMetaR` (`Repair`'s synced tail), but the token's entry of the lent registry deleted with the
registration (`walLentRes_unregLent`): the key comes out of the registry and is consumed by the
unregistration; the WAL's `IdleZ0` from the registered entry's `TailZ0`.

* `walLentRes_unregLent`: the registry without the entry, the registration of `dir` gone;
* `walTailsRes_closeL`: `walTailsRes_close` by the token;
* `walInvBody_untailL`: `walInvBody_untail` by the token (the tail idle: exact, all written, every byte
  durable, the zeros known only past its end);
* `walInv_repairPut`: `Repair`'s put-back after its truncate and fsync, by the pending token (P6: the
  synced layout may keep a pending run past `wr`, so no F-Z and no key), then the pin put back.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseLaw
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandlePend
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairPin

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section law
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **A lent tail's entry deleted with its registration** (see the file header). -/
theorem walLentRes_unregLent (T : GMap GoString GName) (Ls : GMap GoString WalLay) (dir : GoString)
    (γ : GName) (k : Nat) (p : Bool) (hz0 : ∀ lay, Ls !! dir = some lay → TailZ0 lay) :
    ⊢ walLentTokB (W := W) dir γ k p -∗ walLentRes (W := W) T Ls ==∗
      walTailKey (W := W) dir γ ∗ walLentRes (W := W) (GMap.delete dir T) Ls := by
  unfold walLentRes
  iintro Hl ⟨%M, Ha, %HZ, %HI, Hm⟩
  icases walLentTok_lookup M dir γ k p $$ Ha Hl with %hM
  ihave ⟨⟨-, Hk⟩, Hm⟩ := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (x : GName × Nat × Bool) =>
    iprop(⌜LentOk T Ls dir x⌝ ∗ walTailKey (W := W) dir x.1)) hM).1 $$ Hm
  imod walLentTok_delete M dir γ k p $$ Ha Hl with Ha
  imodintro
  iframe Hk
  iexists _
  iframe Ha
  isplitr
  · ipureintro
    intro d la hT hla hp
    by_cases e : d = dir
    · subst e; exact absurd (GMap.lookup_delete_eq _ _) hT
    · rw [GMap.lookup_delete_ne _ (Ne.symm e)] at hT
      exact zerosOr_congr (GMap.lookup_delete_ne _ (Ne.symm e))
        (HZ d la hT hla (fun x hx => hp x (by rw [GMap.lookup_delete_ne _ (Ne.symm e)]; exact hx)))
  isplitr
  · ipureintro
    intro d la hT hla
    by_cases e : d = dir
    · subst e; exact hz0 la hla
    · rw [GMap.lookup_delete_ne _ (Ne.symm e)] at hT; exact HI d la hT hla
  iapply BigSepM.bigSepM_mono (fun {k' x} hk => ?_) $$ Hm
  iintro ⟨%hx, Hk⟩
  iframe Hk
  ipureintro
  have e : k' ≠ dir := by
    change GMap.delete dir M !! k' = some x at hk; rintro rfl; rw [GMap.lookup_delete_eq] at hk; cases hk
  obtain ⟨hT, hl⟩ := hx
  exact ⟨by rw [GMap.lookup_delete_ne _ (Ne.symm e)]; exact hT, hl⟩

/-- **The open handle's tail record removed by the lent token** (`walTailsRes_close` with the token in
place of the key; see the file header). -/
theorem walTailsRes_closeL (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState) (Ls : GMap GoString WalLay)
    (F : GMap Ino SegFl) (dir : GoString) (γ γt : GName) (k : Nat) (p : Bool) (tg : TailG) :
    ⊢ walTailsRes (W := W) C Mr s Ls F -∗ walTailsFrag (W := W) (<[dir := γt]> ∅) -∗
      walLentTokB (W := W) dir γ k p -∗ tailVar (W := W) γ tg -∗
      ∃ (d : WalDur) (lay : WalLay) (g : SegG),
        ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧
          tg = tailG d lay g.ino (F !! g.ino) ∧ TailsOnly (<[dir := γt]> (∅ : GMap GoString GName)) Ls F⌝ ∗
        (⌜TailIdle C Mr d lay ∧ F !! g.ino = none⌝ ==∗ walTailsRes (W := W) C Mr s Ls F ∗ walTailsFrag (W := W) ∅) := by
  letI := walAllG (W := W)
  unfold tailVar
  iintro Htl Htf Hk Hv
  unfold walTailsRes
  icases Htl with ⟨%T, HTa, %HTo, %HTi, HTm, HL⟩
  icases walTails_agree (W := W) T _ $$ HTa Htf with %hT
  subst hT
  icases walLentRes_lookup _ Ls dir γ k p $$ Hk HL with ⟨%hlk, Hk, HL⟩
  have HT := hlk.1.1
  have hγ : γt = γ := by
    simp only at HT
    rw [GMap.lookup_insert] at HT; cases HT; rfl
  subst hγ
  ihave ⟨Hent, HTm⟩ := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (γ : GName) =>
    iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZ0 lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).1 $$ HTm
  icases Hent with ⟨%d, %lay, %g, %hp, Hv'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Htg
  iexists d, lay, g
  isplitr
  · ipureintro; exact ⟨hp.1, hp.2.1, hp.2.2.1, Htg, HTo⟩
  iintro %hidle
  imod walLentRes_unregLent (W := W) _ Ls dir γt k p
    (fun la hla => by rw [hp.2.1] at hla; cases hla; exact hp.2.2.2.1) $$ Hk HL with ⟨Hk, HL⟩
  rw [tailsDel_single dir γt]
  have hu := walTails_unregister (W := W) (<[dir := γt]> ∅) dir γt
  rw [tailsDel_single] at hu
  imod hu $$ HTa Htf Hk with ⟨HTa, Htf⟩
  imodintro
  iframe Htf
  iexists ∅
  iframe HTa HL
  isplitr
  · ipureintro
    have hF0 := tailsOnly_single_none hp.2.1 hp.2.2.1 hidle.2 HTo
    intro i hi
    exact absurd (by rw [hF0]; exact GMap.lookup_empty i) hi
  isplitr
  · ipureintro
    intro k d' lay' _ hd' hl'
    by_cases e : dir = k
    · subst e
      rw [hp.1] at hd'; cases hd'
      rw [hp.2.1] at hl'; cases hl'
      exact hidle.1
    · exact HTi k d' lay' (GMap.lookup_insert_ne _ _ e) hd' hl'
  · iapply BigSepM.bigSepM_empty.2; iempintro

/-- **The open handle's tail unregistered by the lent token** at the body (`walInvBody_untail` with the
token; see the file header). -/
theorem walInvBody_untailL (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (s : AbsDiskState)
    (dir : GoString) (γ γt : GName) (k : Nat) (p : Bool) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (wr : Nat) (ino : Ino) (m : OsMeta) (bs : List ByteG)
    (hTM : TailMetaR m bs ∧ (∀ z, m.zf = some z → m.size ≤ z) ∧ ∀ y ∈ bs, y = Fs.durB y.1)
    (hwr : wr = (tailStream Mr H md cuts).length) :
    ⊢ walInvBody (L := L) (W := W) walCodec Mr R jr r s -∗ walTailsFrag (W := W) (<[dir := γt]> ∅) -∗
      walLentTokB (W := W) dir γ k p -∗ tailVar (W := W) γ ((H, md, cuts, wr, ino, none) : TailG) -∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m -∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs ==∗
      ∃ d : WalDur, ⌜s.wal !! dir = some d ∧ d.H = H⌝ ∗ walInvBody (L := L) (W := W) walCodec Mr R jr r s ∗
        walTailsFrag (W := W) ∅ ∗ osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗
        osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs := by
  iintro Hb Htf Hk Hv Hm Hbs
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    HK, %HAt, Hnms, %Hbd⟩
  icases walTailsRes_closeL (W := W) walCodec Mr s Ls F dir γ γt k p _ $$ Htl Htf Hk Hv with
    ⟨%d, %lay, %g, %hp, Hclose⟩
  obtain ⟨hd, hl, hg, htg, hTO⟩ := hp
  simp only [tailG, Prod.mk.injEq] at htg
  obtain ⟨hH, hmd, hcuts, hwr', hino, hF⟩ := htg
  have hF0 : F = ∅ := tailsOnly_single_none hl hg hF.symm hTO
  subst hF0 hH hmd hcuts hwr' hino
  icases (laysResF_empty (L := L) Ls).1 $$ Hlays with Hlays
  icases (laysRes_list (L := L) Ls).1 $$ Hlays with Hlays
  have hgm : g ∈ segsAll Ls := mem_segsAll hl (List.mem_of_getLast? hg)
  have hsz := walsOk_segs_size HW g hgm
  icases (BigSepL.bigSepL_mem_acc (Φ := fun g => segRes (L := L) g) hgm) $$ Hlays with ⟨Hg1, Hlays⟩
  iunfold segRes at Hg1
  icases Hg1 with ⟨Hm2, Hb2⟩
  icases parked_osMeta_agree (L := L) g.ino _ _ m g.om $$ Hm Hm2 with %hgom
  subst hgom
  icases osBytes_agree (L := L) g.ino _ _ 0 bs g.bs (by rw [hTM.1.1, hsz]) $$ Hbs Hb2 with %hbb
  subst hbb
  ihave Hlays := Hlays $$ [Hm2 Hb2]
  · iunfold segRes; iframe Hm2 Hb2
  have hex : SegExact g := ⟨by rw [← hsz]; exact hTM.1.2.2.1, by rw [← hsz]; exact hTM.1.2.2.2⟩
  have hidle : TailIdle walCodec Mr d lay := by
    refine ⟨fun g' hg' => ?_, ?_, fun g' hg' => ?_, ?_, fun g' hg' => ?_⟩
    · rw [hg] at hg'; cases hg'; exact hex
    · rw [hwr, tailStream_eq]
    · rw [hg] at hg'; cases hg'
      exact ⟨hTM.2.2, fun z hz => by rw [← hsz]; exact hTM.2.1 z hz⟩
    · obtain ⟨lay', nm, hj, hl', -, -, -, -, habs, -⟩ := HW.1 _ _ hd
      rw [hl] at hl'; cases hl'
      exact ((habs.last g hg).1 hex).so_eq hTM.2.2
    · rw [hg] at hg'; cases hg'; exact hTM.1.2.1
  imod Hclose $$ %(⟨hidle, GMap.lookup_empty _⟩ : TailIdle walCodec Mr d lay ∧ (∅ : GMap Ino SegFl) !! g.ino = none) with ⟨Htl, Htf⟩
  ihave Hlays := (laysRes_list (L := L) Ls).2 $$ Hlays
  ihave Hlays := (laysResF_empty (L := L) Ls).2 $$ Hlays
  imodintro
  iexists d
  isplitr
  · ipureintro; exact ⟨hd, rfl⟩
  iframe Htf Hm Hbs
  iexists Ls, cl, n, ∅
  iframe Hg Hcl Hcm HCR Htl Hpk Hlays HK Hnms
  isplitr
  · ipureintro; exact Har
  isplitr
  · ipureintro; exact HW
  isplitr
  · ipureintro; exact HWC
  isplitr
  · ipureintro; exact Hab
  isplitr
  · ipureintro; exact HNm
  ipureintro; exact ⟨HAt, Hbd⟩

/-- **`Repair`'s put-back after its truncate and fsync** (see the file header), at a program step: the
tail unregistered by the pending token (`walInvBody_untailL`: the synced layout F-Z, or `TailPend` with
the pending run `Repair` kept, P6), then the pin put back with the synced segment
(`walInv_unpinLast`); the free lock token out. -/
theorem walInv_repairPut (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (wr : Nat) (m : OsMeta) (bs : List ByteG) (j : Ino) (X : List GoString) (hj : NamesH) (gL : SegG)
    (I : GMap GoString Nat)
    (hTM : TailMetaR m bs ∧ (∀ z, m.zf = some z → m.size ≤ z) ∧ ∀ y ∈ bs, y = Fs.durB y.1)
    (hwr : wr = (tailStream Mr H md cuts).length) :
    ⊢ walInv (L := L) (W := W) walCodec Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walTailsFrag (W := W) (<[dir := γ]> ∅) -∗ walLentTokB (W := W) dir γ k true -∗
      tailVar (W := W) γ ((H, md, cuts, wr, gL.ino, none) : TailG) -∗
      osMeta (L := L) gL.ino (DFrac.own (1 : Qp).half) m -∗
      osBytes (L := L) gL.ino 0 (DFrac.own (1 : Qp).half) bs -∗
      walLockedTokI (W := W) I -∗ walNamesFrag (W := W) none -∗
      walOutFrag (W := W) ⟨[gL.ino], [(j, .except X)], []⟩ -∗
      osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj -∗
      walDirKey (W := W) dir (incOf I dir) j X ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ walUnlockedTok (W := W) := by
  iintro #Hinv Hnc Htf Hk Hv Hm Hbs Hl Hn Ho Hns #Hdk
  imod walInv_open walCodec Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  imod walInvBody_untailL Mr R jr r s dir γ γ k true H md cuts wr gL.ino m bs hTM hwr $$ Hb Htf Hk Hv Hm Hbs
    with ⟨%d, -, Hb, Htf, Hm, Hbs⟩
  imod Hcl $$ [Hb]
  · iexists s; iexact Hb
  iapply walInv_unpinLast walCodec Mr R jr r dir j X hj ({ gL with om := m, bs := bs } : SegG)
    hTM.1.1.symm I $$ Hinv Hnc Hl [Htf Hn] Ho [Hm Hbs] Hns Hdk
  · iframe
  · unfold segRes; iframe

end law

end WalFs
end EtcdGrove
end Perennial

end
