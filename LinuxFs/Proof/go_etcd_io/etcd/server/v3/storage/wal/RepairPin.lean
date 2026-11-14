/- Lean-first (no Rocq counterpart).

# `Repair`'s pin of the last segment (law L1 of `wal.Repair`, W7 of `notes/wal-fsext-plan.md`)

`Repair`'s `openLast` reads the WAL directory's names and opens its last segment read-write. As
`openAtIndex` (`OpenAtPin.lean`), the proof commits the client's update and pins the WAL at the first
step, here from its last segment on (`k lay = |segs| - 1`), in read mode (no pipeline names, no open-WAL
record): `walInv_openLast`. The update commits unchanged (`Repair` changes no WAL state).

What the pin hands the program (`walPinLast`) is `walInvBody_pin`'s, the segments one, the last; and the
WAL's tail is idle (`TailIdle`: no handle holds it, the tails' program half being empty, `walTailsRes`'s
`WalTailIdle`), which law L2 (`RepairDecode.lean`, `walRepairFile`) needs: `walInvBody_pinIdle`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtPin
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllLaws
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtSteps

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- The position of the last segment. -/
def walLastK (lay : WalLay) : Nat := lay.segs.length - 1

/-- From the last position on, the last segment. -/
theorem drop_walLastK {lay : WalLay} {g : SegG} (hg : lay.segs.getLast? = some g) :
    lay.segs.drop (walLastK lay) = [g] := by
  unfold walLastK
  rw [List.getLast?_eq_getElem?] at hg
  have hne : lay.segs ≠ [] := by intro h; rw [h] at hg; simp at hg
  have hl : 0 < lay.segs.length := List.length_pos_iff.2 hne
  rw [List.drop_eq_getElem_cons (by omega), List.getElem?_eq_getElem (by omega)] at *
  injection hg with hg
  rw [hg, List.drop_eq_nil_of_le (by omega)]

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **What the pin of the last segment hands the program** (see the file header): the layout `lay` of
the WAL `d` (its directory's claim `(lay.j, .except X, hj)`), its tail idle, its last segment `gL`; the
WAL's key, the lock token, the tails' and names' program halves, the out record of the last segment and
of the directory's claim, the program's halves of `gL` and of the claim. -/
def walPinLast (C : WalCodec) (Mr : WalMarshal) (jr : Ino) (dir : GoString) (d : WalDur) : IProp GF :=
  iprop(∃ (lay : WalLay) (X : List GoString) (hj : NamesH) (gL : SegG),
    ⌜lay.jr = jr ∧ (∀ b ∈ X, walNameP b = false) ∧
      ClaimCoh hj lay.j (.except X) ∧ WalAbsD C Mr d lay hj.cur ∧ TailIdle C Mr d lay ∧
      (lay.segs.map (·.ino)).Nodup ∧ SegsNamed lay.segs hj.cur ∧ lay.segs.getLast? = some gL⌝ ∗
    walDirKey (W := W) dir lay.j X ∗ walLockedTok (W := W) ∗
    (walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) ∗
    walOutFrag (W := W) ⟨[gL.ino], [(lay.j, .except X)], []⟩ ∗
    segRes (L := L) gL ∗ osNames (L := L) lay.j (.except X) (DFrac.own (1 : Qp).half) hj)

/-- **The pin, in read mode, with the tail idle** (`walInvBody_pin` at `write = false`, and
`walTailsRes_idle` on the tails' authority, whose program half the lock hands out empty). -/
theorem walInvBody_pinIdle (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (d : WalDur) (hd : s.wal !! dir = some d) (k : WalLay → Nat) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walUnlockedTok (W := W) ==∗
      ∃ (lay : WalLay) (X : List GoString) (hj : NamesH),
        ⌜InArea s.area dir lay.nm ∧ lay.jr = jr ∧ (∀ b ∈ X, walNameP b = false) ∧
          ClaimCoh hj lay.j (.except X) ∧ WalAbsD C Mr d lay hj.cur ∧ TailIdle C Mr d lay ∧
          (lay.segs.map (·.ino)).Nodup ∧ SegsNamed lay.segs hj.cur⌝ ∗ walDirKey (W := W) dir lay.j X ∗
        walInvBody (L := L) (W := W) C Mr R jr r s ∗ walLockedTok (W := W) ∗ walTailsFrag (W := W) ∅ ∗
        walNamesFrag (W := W) none ∗
        walOutFrag (W := W) ⟨(lay.segs.drop (k lay)).map (·.ino), [(lay.j, .except X)], []⟩ ∗
        ([∗list] g ∈ lay.segs.drop (k lay), segRes (L := L) g) ∗
        osNames (L := L) lay.j (.except X) (DFrac.own (1 : Qp).half) hj := by
  iintro Hb Hu
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hn, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    Hdk, %HAt, Hnms, %Hbd⟩
  obtain ⟨lay, nm, hj, hl, hA, hjr, hnm, hc, habs, hcr⟩ := HW.1 dir d hd
  obtain ⟨X, hX, hcX, hcoh⟩ := hc
  icases Hdk with ⟨%K, %cp, HKa, Hca, %HDK⟩
  imod walDirKeys_pin C Mr jr s Ls cl n K cp dir lay X hj HDK hl hX hcX $$ HKa with ⟨%K', HKa, %HDK', #Hkey⟩
  imod walParked_lock (L := L) (W := W) Ls cl F $$ Hpk Hu with ⟨Hpk, Hl, Ho, Htf, Hnf, %hF⟩
  icases walTailsRes_idle C Mr s Ls F $$ Htl Htf with ⟨%hidle, Htl, Htf⟩
  have hF0 : F = ∅ := (GMap.lookup_empty_iff F).1 hF
  subst hF0
  have hS : ∀ g ∈ lay.segs.drop (k lay), g ∈ segsAll Ls := fun g hg =>
    mem_segsAll hl (List.mem_of_mem_drop hg)
  have hnd : ((lay.segs.drop (k lay)).map (·.ino)).Nodup := by
    rw [List.map_drop]
    exact (((segsAll_nodup_iff Ls).1 HW.2.2.1).1 dir lay hl).sublist (List.drop_sublist _ _)
  imod walParked_takeSegs (L := L) (W := W) Ls cl ∅ WalOut.empty (lay.segs.drop (k lay)) hS
    (fun _ _ h => by cases h) hnd $$ Hpk Ho with ⟨Hpk, Ho, HS, -⟩
  imod walParked_takeClaim (L := L) (W := W) Ls cl ∅ _ (lay.j, .except X, hj) hcX
    ⟨dir, lay, hl, rfl, X, rfl, hX⟩ (by simp [WalOut.empty]) $$ Hpk Ho with ⟨Hpk, Ho, Hnm⟩
  icases (laysResF_del (L := L) ∅ Ls dir lay hl).1 $$ Hlays with ⟨Hsegs, Hrest⟩
  ihave Hsegs := BigSepL.bigSepL_mono (fun {_ g} _ => (segResF_empty (L := L) g).1) $$ Hsegs
  icases (bigSepL_take_drop (fun g => segRes (L := L) g) lay.segs (k lay)).1 $$ Hsegs with ⟨Hpre, Hpost⟩
  icases segsRes_exact (L := L) (lay.segs.drop (k lay)) $$ [Hpost HS] with ⟨Hpost, HS⟩
  · iframe Hpost HS
  ihave Hlays := (laysResF_del (L := L) ∅ Ls dir lay hl).2 $$ [Hpre Hpost Hrest]
  · iframe Hrest
    iapply BigSepL.bigSepL_mono (fun {_ g} _ => (segResF_empty (L := L) g).2)
    iapply (bigSepL_take_drop (fun g => segRes (L := L) g) lay.segs (k lay)).2
    iframe Hpre Hpost
  have hpure : InArea s.area dir lay.nm ∧ lay.jr = jr ∧ (∀ b ∈ X, walNameP b = false) ∧
      ClaimCoh hj lay.j (.except X) ∧ WalAbsD C Mr d lay hj.cur ∧ TailIdle C Mr d lay ∧
      (lay.segs.map (·.ino)).Nodup ∧ SegsNamed lay.segs hj.cur := by
    rw [hnm]
    exact ⟨hA, hjr, hX, hcoh, habs, hidle dir d lay hd hl,
      ((segsAll_nodup_iff Ls).1 HW.2.2.1).1 dir lay hl, (HNm dir lay hl).1 hj ⟨X, hX, hcX, hcoh⟩⟩
  imodintro
  iexists lay, X, hj
  iframe HS Hnm Hl Htf Hnf Hkey
  isplitr
  · ipureintro; exact hpure
  isplitl [Hg Hcl Hn Hlays HCR Htl Hpk HKa Hca Hnms]
  · iexists Ls, cl, n, ∅
    iframe
    ipureintro; exact ⟨Har, HW, HWC, Hab, HNm, HDK', HAt, Hbd⟩
  · iapply walOutFrag_eq' (W := W) $$ Ho
    ipureintro; simp [WalOut.empty, WalOut.addClaim]

/-- **The pin of the last segment, as `walPinLast`.** -/
theorem walInvBody_pinLast (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (d : WalDur) (hd : s.wal !! dir = some d) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walUnlockedTok (W := W) ==∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ walPinLast (L := L) (W := W) C Mr jr dir d := by
  iintro Hb Hu
  imod walInvBody_pinIdle C Mr R jr r s dir d hd walLastK $$ Hb Hu with
    ⟨%lay, %X, %hj, %hp, Hkey, Hb, Hl, Htf, Hnf, Ho, HS, Hj⟩
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := hp
  obtain ⟨gL, hgL⟩ : ∃ gL, lay.segs.getLast? = some gL := by
    cases h : lay.segs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 h) h4.nonempty
    | some g => exact ⟨g, rfl⟩
  rw [drop_walLastK hgL, List.map_cons, List.map_nil]
  imodintro
  iframe Hb
  unfold walPinLast
  iexists lay, X, hj, gL
  icases BigSepL.bigSepL_cons.1 $$ HS with ⟨HS, -⟩
  iframe Hkey Hl Htf Hnf Ho HS Hj
  ipureintro; exact ⟨h1, h2, h3, h4, h5, h6, h7, hgL⟩

/-- **`Repair`'s update and pin** (see the file header): the update committed unchanged; the WAL
absent (the area holds nothing at `nm`, the token kept), or the pin of its last segment. -/
theorem walInv_openLast (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir nm : GoString) (N : NameSet) (dq : DFrac)
    (h : NamesH) (Wn : List GoString) (Q : Option WalDur → IProp GF)
    (hin : InArea r dir nm) (hN : N.Mem nm ∨ nm ∈ Wn) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗ walUnlockedTok (W := W) -∗
      (AU <{ ∃∃ o : Option WalDur, walDirIs (W := W) dir o }> @ walAuMask, ∅
        <{ walDirIs (W := W) dir o, COMM Q o }>) -∗
      osNames (L := L) jr N dq h -∗ walSplitFrag (W := W) Wn ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ osNames (L := L) jr N dq h ∗ walSplitFrag (W := W) Wn ∗
      ∃ o : Option WalDur, Q o ∗
        ((⌜o = none ∧ N.Mem nm ∧ h.cur !! nm = none⌝ ∗ walUnlockedTok (W := W)) ∨
         (⌜o ≠ none⌝ ∗ ∃ d, walPinLast (L := L) (W := W) C Mr jr dir d)) := by
  iintro #Hinv #Hsi Hnc Hu Hau Hn Hsf
  imod walInv_open C Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  imod walInvBody_areaAt C Mr R jr r s dir nm N dq h Wn hin hN walN_osShN_top' $$ Hb Hsi Hn Hsf
    with ⟨Hb, Hn, Hsf, %Hat⟩
  ihave Hau := atomic_update_mask_weaken walAuMask_sub_top' $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%o, Ho, Hucl⟩
  unfold walDirIs
  icases Ho with ⟨%M, HM, %HMd⟩
  icases walInvBody_mapLe C Mr R jr r s M $$ Hb HM with ⟨%HMs, Hb, HM⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  imod Hcommit $$ [HM] with HQ
  · iexists M; iframe HM; ipureintro; exact HMd
  cases o with
  | none =>
    have hMd : M !! dir = none := (walOptLe_none_iff _).1 HMd
    have hsd : s.wal !! dir = none := by
      have := HMs dir; rw [hMd] at this; exact (walOptLe_none_iff _).1 this
    imod Hcl $$ [Hb] with -
    · iexists s; iexact Hb
    imodintro
    iframe Hnc Hn Hsf
    iexists none
    iframe HQ
    ileft
    iframe Hu
    ipureintro; exact ⟨rfl, Hat hsd⟩
  | some dc =>
    obtain ⟨d0, hM0, hle0⟩ := (walOptLe_some_iff _ _).1 HMd
    obtain ⟨ds, hsd⟩ : ∃ ds, s.wal !! dir = some ds := by
      have h1 := HMs dir
      rw [hM0] at h1
      obtain ⟨ds, hds, -⟩ := (walOptLe_some_iff _ _).1 h1
      exact ⟨ds, hds⟩
    imod walInvBody_pinLast C Mr R jr r s dir ds hsd $$ Hb Hu with ⟨Hb, Hp⟩
    imod Hcl $$ [Hb] with -
    · iexists s; iexact Hb
    imodintro
    iframe Hnc Hn Hsf
    iexists (some dc)
    iframe HQ
    iright
    isplitr
    · ipureintro; simp
    iexists ds; iexact Hp

/-- **The put-back of the pinned last segment, unchanged** (law L5 where `Repair` changed nothing:
`walInv_unpin` in read mode, one segment). -/
theorem walInv_unpinLast (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (gL : SegG)
    (hS : gL.om.size = gL.bs.length) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walLockedTok (W := W) -∗ (walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) -∗
      walOutFrag (W := W) ⟨[gL.ino], [(j, .except X)], []⟩ -∗
      segRes (L := L) gL -∗ osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj -∗
      walDirKey (W := W) dir j X ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ walUnlockedTok (W := W) := by
  iintro #Hinv Hnc Hl Htf Ho HS Hn #Hk
  iapply walInv_unpin C Mr R jr r dir j X hj [gL] false (by simpa using hS) $$ Hinv Hnc Hl Htf
    [Ho] [HS] Hn [] Hk
  · simp only [List.map_cons, List.map_nil, Bool.false_eq_true, ↓reduceIte]; iexact Ho
  · iapply BigSepL.bigSepL_cons.2; iframe HS; iapply BigSepL.bigSepL_nil.2; iempintro
  · simp only [Bool.false_eq_true, ↓reduceIte]; iempintro

end iris

end WalFs
end EtcdGrove
end Perennial

end
