/- Lean-first (no Rocq counterpart).

# The cleanup's pin and its rename's update (W4, `notes/wal-units/create.md`, session 4)

* `walInvBody_pinClean`: the cleanup's pin. `Create`'s half of an area claim `(jr, N, h)` holding a
  WAL name is the invariant's other half (`WalsCreateOk`, `osClaims_keys`), once, coherent, exclusive
  on its names: recorded in the creating map at `cleanKey` (`CreatingOk`), the free token less its
  names fragment deposited (`walCreating_mintC`), where the shared invariant is available.
* `cleanAU`: the update `cleanupWAL`'s `os.Rename.specDirAnySnc` (of `nm`, holding the WAL's directory
  `J`, onto `brk`) takes. Opened (with `notCrashed`), it opens `walInv`, finds the pinned claim among
  the invariant's (`walCleanPin_lookup`, `CreatingOk`) and hands out its half. An abort closes it again;
  a commit deletes the pin (`walCreating_deleteC`: the token back) and, the rename logged, replaces the
  claim by its logged self (`movClaims`; the WAL known present by `AbsentNone`, unnamed by
  `walNamesRes_unnamed` with `Create`'s names fragment): `CleanupMoved.lean`'s facts.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CleanupMoved
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAu
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSteps

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

/-- **The cleanup's pin** (see the file header). -/
theorem walInvBody_pinClean (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (N : NameSet) (h : NamesH) (b : GoString) {Em : CoPset}
    (hb : walNameOk b) (hN : N.Mem b) (hE : ↑osShN ⊆ Em) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ osSharedInv (L := L) R -∗ walUnlockedTokX (W := W) -∗
      osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ={Em}=∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ walCleanPin (W := W) N h jr ∗
        osNames (L := L) jr N (DFrac.own (1 : Qp).half) h := by
  classical
  have hNe : N ≠ .only [] := nameSet_ne_empty hN
  unfold walInvBody
  iintro Hb #Hsi Hu H
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %hr, Hcl, Hn, HF, %hwo, %hwc, ⟨%CR, HCRa, %hCR⟩, Htl, %hab,
    %hwn, Hpk, Hdk, %hAt, Hnms, %Hbd⟩
  imod osClaims_keys R jr N _ h _ hNe hE $$ Hsi H Hcl with ⟨H, Hcl, %hk⟩
  have hm : ((jr, N, h) : Claim) ∈ cl := by
    obtain ⟨M, g, hm, hM⟩ := hwc b hb
    obtain ⟨e1, e2⟩ := hk ((jr, M, g), _) (List.mem_map_of_mem hm) rfl b hN hM
    simp only at e1 e2
    rw [e1, e2] at hm; exact hm
  icases osClaims_once (L := L) cl (jr, N, h) hNe hm $$ H Hcl with ⟨%ho, H, Hcl⟩
  imod osNames_coh R jr N _ h hE $$ Hsi H with ⟨H, %hcoh⟩
  imod walCreating_mintC CR N h jr $$ HCRa Hu with ⟨%hCR0, HCRa, Hpin⟩
  have hcok : CreatingOk jr cl
      (<[cleanKey := (N, h, jr)]> (∅ : GMap GoString (NameSet × NamesH × Ino))) := by
    intro dir N' h' J' hl'
    by_cases hd : dir = cleanKey
    · subst hd
      rw [GMap.lookup_insert_eq] at hl'
      simp only [Option.some.injEq, Prod.mk.injEq] at hl'
      obtain ⟨rfl, rfl, rfl⟩ := hl'
      refine ⟨hm, hcoh, fun c hc hne hj b' hb' hcb => hne ?_, ho, fun d2 J2 hd2 => ?_,
        fun hk' => absurd rfl hk'⟩
      · obtain ⟨e1, e2⟩ := hk (c, _) (List.mem_map_of_mem hc) hj b' hb' hcb
        obtain ⟨c1, c2, c3⟩ := c
        simp only at hj e1 e2
        rw [hj, e1, e2]
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hd2)]; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hd)] at hl'; simp at hl'
  imodintro
  iframe Hpin H
  iexists Ls, cl, n, F
  iframe Hg Hcl Hn HF Htl Hpk Hdk Hnms
  isplitr
  · ipureintro; exact hr
  isplitr
  · ipureintro; exact hwo
  isplitr
  · ipureintro; exact hwc
  isplitl [HCRa]
  · iexists _; iframe HCRa; ipureintro; exact hcok
  isplitr
  · ipureintro; exact hab
  isplitr
  · ipureintro; exact hwn
  ipureintro; exact ⟨hAt, Hbd⟩

/-- The cleanup's pin, at a program step. -/
theorem walInv_pinClean (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (N : NameSet) (h : NamesH) (b : GoString) (hb : walNameOk b) (hN : N.Mem b) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗ walUnlockedTokX (W := W) -∗
      osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ walCleanPin (W := W) N h jr ∗
        osNames (L := L) jr N (DFrac.own (1 : Qp).half) h := by
  iintro #Hinv #Hsi Hnc Hu H
  iapply walInv_step C Mr R jr r
    iprop(osSharedInv (L := L) R ∗ walUnlockedTokX (W := W) ∗
      osNames (L := L) jr N (DFrac.own (1 : Qp).half) h)
    iprop(walCleanPin (W := W) N h jr ∗ osNames (L := L) jr N (DFrac.own (1 : Qp).half) h)
    ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb ⟨#Hsi, Hu, H⟩
      iapply walInvBody_pinClean C Mr R jr r s N h b hb hN walN_osShN_top $$ Hb Hsi Hu H)
    $$ Hinv Hnc [Hu H]
  iframe Hu H; iexact Hsi

end iris

section au
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- What the cleanup's update holds: the pin and the pending registration. -/
def cleanP (dir : GoString) (N : NameSet) (h : NamesH) (jr : Ino) : IProp GF :=
  iprop(walCleanPin (W := W) N h jr ∗ walNamesFrag (W := W) (some dir))

/-- What the cleanup's update gives back, whatever the outcome: the token, the pending registration. -/
def cleanQ (dir : GoString) (_o : Option (Nat × Nat)) : IProp GF :=
  iprop(walUnlockedTokX (W := W) ∗ walNamesFrag (W := W) (some dir))

/-- **The cleanup's rename's update** (see the file header). -/
theorem cleanAU (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir nm brk : GoString) (N : NameSet) (h : NamesH) (J : Ino) (lb : Nat)
    (hin : InArea r dir nm) (hne : nm ≠ brk) (hnmN : N.Mem nm) (hbN : N.Mem brk)
    (hJ : h.cur !! nm = some (.dir J)) (hlb : h.next ≤ lb) (hbrk : ¬ walNameOk brk)
    (hbS : AreaSlot brk) :
    ⊢ walInv (W := W) C Mr R jr r -∗ cleanP (W := W) dir N h jr -∗
      osAUnc (osNames jr N (DFrac.own (1 : Qp).half) h)
        (renDirOutA jr J N nm brk h (DFrac.own (1 : Qp).half) lb) (cleanQ (W := W) dir) := by
  classical
  iintro #Hinv HP
  iapply osAUnc_coiter _ _ _ (cleanP (W := W) dir N h jr) $$ [] HP
  iintro !> HP
  unfold osAUncPre
  iintro Hnc
  imod walInv_open C Mr R jr r osAuMask walN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  rw [show osAuMask \ (↑walN : CoPset) = walAuMask from rfl]
  icases Hb with ⟨%s, Hb⟩
  unfold cleanP
  icases HP with ⟨Hpin, Hnf⟩
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl0, #Hcm, Hlays, %Hok, %Hco, ⟨%CR, Hcra, %Hcro⟩,
    Htl, %Han, %Hnm, Hpk, ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  icases walCleanPin_lookup CR N h jr $$ Hcra Hpin with ⟨%Hcr, Hcra, Hpin⟩
  have hco := Hcro
  obtain ⟨hc, hcoh, hexcl, honce, -, -⟩ := Hcro cleanKey N h jr Hcr
  obtain ⟨l1, l2, hcl, hl1, hl2⟩ := honce
  subst hcl
  icases (osClaims_split _ _ _ _).1 $$ Hcl0 with ⟨Hl1, Hα, Hl2⟩
  imod (fupd_mask_subseteq (show (∅ : CoPset) ⊆ walAuMask from
    Std.LawfulSet.empty_subset)) with Hmc
  imodintro
  isplitl [Hα]
  · iexact Hα
  iframe Hnc
  isplit
  · -- abort
    iintro Hα
    imod Hmc
    imod Hcl $$ [Hg Hl1 Hα Hl2 Hlays Hcra Htl Hpk Hdk Hcp Hnms]
    · iexists s
      iexists Ls, l1 ++ (jr, N, h) :: l2, n, F
      iframe Hg Hcm Hlays Htl Hpk
      isplitr
      · ipureintro; exact Har
      isplitl [Hl1 Hα Hl2]
      · iapply (osClaims_split _ _ _ _).2
        iframe Hl1 Hα Hl2
      isplitr
      · ipureintro; exact Hok
      isplitr
      · ipureintro; exact Hco
      isplitl [Hcra]
      · iexists CR
        iframe Hcra
        ipureintro; exact hco
      isplitr
      · ipureintro; exact Han
      isplitr
      · ipureintro; exact Hnm
      isplitl [Hdk Hcp]
      · iexists K, cp
        iframe Hdk Hcp
        ipureintro; exact Hdko
      iframe Hnms; ipureintro; exact ⟨HAt, Hbd⟩
    imodintro
    dsimp only
    iframe Hpin Hnf
  · -- commit
    iintro %o Hβ
    imod walCreating_deleteC CR N h jr $$ Hcra Hpin with ⟨%hdel, Hcra, Hu⟩
    rcases o with _ | ⟨x, st⟩
    · -- no effect
      unfold renDirOutA
      simp only [logOut, claimOut]
      icases Hβ with ⟨-, -, Hα⟩
      imod Hmc
      imod Hcl $$ [Hg Hl1 Hα Hl2 Hlays Hcra Htl Hpk Hdk Hcp Hnms]
      · iexists s
        iexists Ls, l1 ++ (jr, N, h) :: l2, n, F
        iframe Hg Hcm Hlays Htl Hpk
        isplitr
        · ipureintro; exact Har
        isplitl [Hl1 Hα Hl2]
        · iapply (osClaims_split _ _ _ _).2
          iframe Hl1 Hα Hl2
        isplitr
        · ipureintro; exact Hok
        isplitr
        · ipureintro; exact Hco
        isplitl [Hcra]
        · iexists _
          iframe Hcra
          ipureintro; intro d N' h' J' hl'; rw [hdel] at hl'; simp at hl'
        isplitr
        · ipureintro; exact Han
        isplitr
        · ipureintro; exact Hnm
        isplitl [Hdk Hcp]
        · iexists K, cp
          iframe Hdk Hcp
          ipureintro; exact Hdko
        iframe Hnms; ipureintro; exact ⟨HAt, Hbd⟩
      imodintro
      unfold cleanQ
      iframe Hu Hnf
    · -- the rename logged: the moved-aside step
      unfold renDirOutA
      simp only [logOut, claimOut]
      icases Hβ with ⟨-, ⟨%hls, -⟩, Hα⟩
      icases walNamesRes_unnamed R jr r Ls s dir $$ Hnms Hnf with ⟨%hun, Hnms, Hnf⟩
      have hin' : InArea s.area dir nm := by rw [Har]; exact hin
      have hpres : s.wal !! dir ≠ none := fun hn => by
        have := (Han.1 dir nm hin' hn).1 N h hc hnmN
        rw [hJ] at this; cases this
      have H : MovedHyp (l1 ++ (jr, N, h) :: l2) jr N h st nm brk J :=
        ⟨hc, hcoh, Nat.le_trans hlb hls,
          fun c' hc' hne' hj => ⟨hexcl c' hc' hne' hj nm hnmN, hexcl c' hc' hne' hj brk hbN⟩,
          hne, hnmN, hbN, hJ⟩
      have hmv : movClaims (l1 ++ (jr, N, h) :: l2) jr N h x st nm brk J =
          l1 ++ (jr, N, h.log x (movEnt jr J nm brk h st) (movCur N h nm brk J)) :: l2 := by
        unfold movClaims; exact replClaim_split hl1 hl2
      have hnW : ∀ c : Claim, c.1 = jr → ¬ WalDirClaimOf Ls c := fun c hc' => HAt.not_walDirClaimOf c hc'
      have hf := filter_replClaim (fun c : Claim => decide (c.1 ≠ jr)) (c0 := (jr, N, h))
        (c1 := (jr, N, h.log x (movEnt jr J nm brk h st) (movCur N h nm brk J))) (by simp) (by simp)
        (l1 ++ (jr, N, h) :: l2)
      ihave Hpk := walParked_cover Ls jr _ _ hnW hf $$ Hpk
      imod Hmc
      imod Hcl $$ [Hg Hl1 Hα Hl2 Hlays Hcra Htl Hpk Hdk Hcp Hnms]
      · iexists s
        iexists Ls, movClaims (l1 ++ (jr, N, h) :: l2) jr N h x st nm brk J, n, F
        unfold movClaims
        iframe Hg Hcm Hlays Htl Hpk
        rw [← movClaims]
        isplitr
        · ipureintro; exact Har
        isplitl [Hl1 Hα Hl2]
        · rw [hmv]
          iapply (osClaims_split _ _ _ _).2
          iframe Hl1 Hl2
          dsimp only [movEnt, movCur]
          iexact Hα
        isplitr
        · ipureintro
          exact walsOk_moved H Hok HAt Han.1 Han.2 hin' hpres hun hbrk hbS
        isplitr
        · ipureintro; exact walsCreateOk_moved Hco
        isplitl [Hcra]
        · iexists _
          iframe Hcra
          ipureintro; intro d N' h' J' hl'; rw [hdel] at hl'; simp at hl'
        isplitr
        · ipureintro; exact ⟨absentNone_moved H Han.1 hin' hpres hbrk, Han.2⟩
        isplitr
        · ipureintro; exact walsNamed_moved H HAt Hnm
        isplitl [Hdk Hcp]
        · iexists K, cp
          iframe Hdk Hcp
          ipureintro; exact dirKeysOk_moved H Hok HAt hin' hun hbrk Hdko
        iframe Hnms; ipureintro; exact ⟨walsAt_moved Hok HAt hin' hbrk hne hc, Hbd⟩
      imodintro
      unfold cleanQ
      iframe Hu Hnf

end au

end WalFs
end EtcdGrove
end Perennial

end
