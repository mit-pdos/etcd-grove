/- Lean-first (no Rocq counterpart).

# `Repair`'s put-back after its truncate and fsync (L5's changed case; the W7-W12 log, thirteenth session)

After `fileutil.Fsync.specRepTail` the program holds the tail's key, its record's half and its synced
halves: `walInvBody_untailR` unregisters the tail (`walInvBody_untail` over `TailMetaR`, the zeros known
from the size on and every byte durable, for `TailMetaS`), then `walInv_unpinLast` puts the pin back with
the synced segment (`RepairPin.lean`). `walInv_untailR` is the first at a step.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseLaw
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandlePend
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairPin

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

/-- **`Repair`'s tail unregistered** at the body: `walInvBody_untail` (`CloseLaw.lean`) with what
`Fsync.specRepTail` gives of the synced tail (`TailMetaR`, the zeros known from the size on, every byte
durable) for `TailMetaS` (which `walInvBody_untail` reads only so far). -/
theorem walInvBody_untailR (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (s : AbsDiskState)
    (dir : GoString) (γ γt : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (wr : Nat) (ino : Ino) (m : OsMeta) (bs : List ByteG)
    (hTM : TailMetaR m bs ∧ (∀ z, m.zf = some z → m.size ≤ z) ∧ ∀ y ∈ bs, y = Fs.durB y.1)
    (hwr : wr = (tailStream Mr H md cuts).length) :
    ⊢ walInvBody (L := L) (W := W) walCodec Mr R jr r s -∗ walTailsFrag (W := W) (<[dir := γt]> ∅) -∗
      walTailKey (W := W) dir γ -∗ tailVar (W := W) γ ((H, md, cuts, wr, ino, none) : TailG) -∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m -∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs ==∗
      ∃ d : WalDur, ⌜s.wal !! dir = some d ∧ d.H = H⌝ ∗ walInvBody (L := L) (W := W) walCodec Mr R jr r s ∗
        walTailsFrag (W := W) ∅ ∗ osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗
        osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs := by
  iintro Hb Htf Hk Hv Hm Hbs
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    HK, %HAt, Hnms, %Hbd⟩
  icases walTailsRes_close (W := W) walCodec Mr s Ls F dir γ γt _ $$ Htl Htf Hk Hv with
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
tail unregistered (`walInvBody_untailR`), then the pin put back with the synced segment
(`walInv_unpinLast`); the free lock token out. -/
theorem walInv_repairPut (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (γ γt : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (wr : Nat) (m : OsMeta) (bs : List ByteG) (j : Ino) (X : List GoString) (hj : NamesH) (gL : SegG)
    (hTM : TailMetaR m bs ∧ (∀ z, m.zf = some z → m.size ≤ z) ∧ ∀ y ∈ bs, y = Fs.durB y.1)
    (hwr : wr = (tailStream Mr H md cuts).length) :
    ⊢ walInv (L := L) (W := W) walCodec Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walTailsFrag (W := W) (<[dir := γt]> ∅) -∗ walTailKey (W := W) dir γ -∗
      tailVar (W := W) γ ((H, md, cuts, wr, gL.ino, none) : TailG) -∗
      osMeta (L := L) gL.ino (DFrac.own (1 : Qp).half) m -∗
      osBytes (L := L) gL.ino 0 (DFrac.own (1 : Qp).half) bs -∗
      walLockedTok (W := W) -∗ walNamesFrag (W := W) none -∗
      walOutFrag (W := W) ⟨[gL.ino], [(j, .except X)], []⟩ -∗
      osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj -∗
      walDirKey (W := W) dir j X ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ walUnlockedTok (W := W) := by
  iintro #Hinv Hnc Htf Hk Hv Hm Hbs Hl Hn Ho Hns #Hdk
  imod walInv_open walCodec Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  imod walInvBody_untailR Mr R jr r s dir γ γt H md cuts wr gL.ino m bs hTM hwr $$ Hb Htf Hk Hv Hm Hbs
    with ⟨%d, -, Hb, Htf, Hm, Hbs⟩
  imod Hcl $$ [Hb]
  · iexists s; iexact Hb
  iapply walInv_unpinLast walCodec Mr R jr r dir j X hj ({ gL with om := m, bs := bs } : SegG)
    hTM.1.1.symm $$ Hinv Hnc Hl [Htf Hn] Ho [Hm Hbs] Hns Hdk
  · iframe
  · unfold segRes; iframe

end law

end WalFs
end EtcdGrove
end Perennial

end
