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

end iris

end WalFs
end EtcdGrove
end Perennial

end
