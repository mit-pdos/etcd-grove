/- Lean-first (no Rocq counterpart).

# `ReleaseLockTo`'s commit with the locked range raised (unit `locks`, session 5)

`ReleaseLockTo(a)` raises the WAL's `unl` to `walReleasePos H a` (`walInv_unlAU`); the handle raises its
registered range with it, to `b' = max b (walReleasePos H a)` (`walLks_set`: within the new `unl`), and
learns, from the layout, that every segment of the directory named below `a` starts at or before `b'`
(`cutStart_le_releasePos`): the locks before the kept one may then go (`LkRel_release`).

* `walInvBody_handleLook`: the open handle's directory claim and tail record against the invariant: the
  layout's static relation over the claim's names, the segments at their names, the record's history and
  cuts the WAL's and the layout's, and the registered ranges within the `unl`s.
* `walInv_releaseLks`: the commit.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReleaseAu
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllGive
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.LockRange
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CutRen
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailSyncIdle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **A segment name of the directory, its index below `a`, starts at or before `walReleasePos`.** -/
theorem absD_name_le_releasePos {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {hj : NamesH}
    (h : WalAbsD C Mr d lay hj.cur) (hsn : SegsNamed lay.segs hj.cur) (hnd : (lay.segs.map (·.ino)).Nodup)
    {sq ix : Nat} {n : Node} {a : w64} (hsq : sq < 2 ^ 64) (hcl : lay.cuts.length < 2 ^ 64)
    (hn : hj.cur !! walFileName sq ix = some n) (hia : uint.nat (W64 ix) < uint.nat a) :
    segStart lay.cuts sq ≤ walReleasePos (histM d) a := by
  obtain ⟨g, hg, hgn⟩ := walName_seg hsn h.names.1 hnd (walNameP_walFileName sq ix) hn
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hg
  have hkl : k < lay.segs.length := (List.getElem?_eq_some_iff.1 hk).1
  have hc := h.cuts.2.2
  obtain ⟨ix1, hix1⟩ := h.seqName k g hk
  obtain ⟨sq2, ix2, hn2, hix2, hb2⟩ := h.nameBound k g hk
  have e1 := walFileName_inj (hgn.trans hix1)
  have e2 := walFileName_inj (hgn.trans hn2)
  have hfk : sq = lay.first + k := by
    have := e1.1
    rw [Nat.mod_eq_of_lt hsq, Nat.mod_eq_of_lt (by omega)] at this
    exact this
  have hix : uint.nat (W64 ix) = ix2 := by
    have : uint.nat (W64 ix) = ix % 2 ^ 64 := by
      show (BitVec.ofNat 64 ix).toNat = _; simp
    rw [this, e2.2, Nat.mod_eq_of_lt hix2]
  subst hfk
  apply cutStart_le_releasePos (ix := ix2)
  rcases Nat.eq_zero_or_pos (lay.first + k) with h0 | h0
  · left; rw [h0]; rfl
  · right
    obtain ⟨hcp, hle⟩ := absD_segStart_cut h h0 (by omega)
    exact ⟨hcp, by simpa [histM] using hle, hb2 h0, by omega⟩

/-- **`ReleaseLockTo`'s step on the locked range**: the first `m` non-tail locks dropped, the range raised to
`b'`, which the first kept lock's segment starts at or before. -/
theorem LkRel_release {hj : NamesH} {cuts : List Nat} {nm0 : GoString} {ls : List (GoString × Ino)}
    {b b' m : Nat} (h : LkRel hj cuts nm0 ls b) (hm : m ≤ ls.length)
    (hb : segStart cuts (cuts.length - ls.length + m) ≤ b') :
    LkRel hj cuts nm0 (ls.drop m) b' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [LkRel, List.length_drop]
  refine ⟨by omega, h2, h3, fun k l hk => ?_, fun nm n hn hw hne hnl => ?_, ?_⟩
  · rw [List.getElem?_drop] at hk
    obtain ⟨hl1, ix, hix⟩ := h4 (m + k) l hk
    exact ⟨hl1, ix, by rw [hix]; congr 1; omega⟩
  · by_cases hin : nm ∈ ls.map (·.1)
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hin
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hl
      have hkl : k < ls.length := (List.getElem?_eq_some_iff.1 hk).1
      rcases Nat.lt_or_ge k m with hkm | hkm
      · obtain ⟨-, ix, hix⟩ := h4 k l hk
        exact ⟨cuts.length - ls.length + k, ix, hix, by omega⟩
      · exfalso; apply hnl
        apply List.mem_map.2 ⟨l, ?_, rfl⟩
        apply List.mem_iff_getElem?.2 ⟨k - m, ?_⟩
        rw [List.getElem?_drop, show m + (k - m) = k by omega]; exact hk
    · obtain ⟨sq, ix, e, hsq⟩ := h5 nm n hn hw hne hin
      exact ⟨sq, ix, e, by omega⟩
  · rw [show cuts.length - (ls.length - m) = cuts.length - ls.length + m by omega]; exact hb

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The open handle's look at the invariant** (see the file header). -/
theorem walInvBody_handleLook (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (j : Ino) (X : List GoString) (hj0 : NamesH) (γ : GName)
    (tg : TailG) (T : GMap GoString GName) (Lk : GMap GoString Nat) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walDirKey (W := W) dir j X -∗
      osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj0 -∗
      walTailKey (W := W) dir γ -∗ tailVar (W := W) γ tg -∗ walTailsFrag (W := W) T Lk -∗
      ⌜(∃ d lay, s.wal !! dir = some d ∧ WalAbsD C Mr d lay hj0.cur ∧ SegsNamed lay.segs hj0.cur ∧
        (lay.segs.map (·.ino)).Nodup ∧ tg.1 = d.H ∧ tg.2.2.1 = lay.cuts) ∧ LksOk s Lk⌝ ∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ walDirKey (W := W) dir j X ∗
      osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj0 ∗
      walTailKey (W := W) dir γ ∗ tailVar (W := W) γ tg ∗ walTailsFrag (W := W) T Lk := by
  iintro Hb #Hk Hn Htk Hv Htf
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  icases walDirKey_lookup K dir j X $$ Hdk Hk with %hK
  obtain ⟨lay, hj, hl, hlj, -, hXw, hOnce, -, hOther⟩ := Hdko.1 dir j X hK
  obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir = some d := by
    cases h : s.wal !! dir with
    | none => rw [HW.2.1 dir h] at hl; cases hl
    | some d => exact ⟨d, rfl⟩
  obtain ⟨lay1, nm, hj', hl1, -, -, -, hWDC, habs, -⟩ := HW.1 dir d hd
  rw [hl] at hl1; cases hl1
  have hjj : hj' = hj := by
    obtain ⟨X', hX', hmem, -⟩ := hWDC
    by_cases hc : (lay.j, NameSet.except X', hj') = (j, NameSet.except X, hj)
    · simp only [Prod.mk.injEq] at hc; exact hc.2.2
    · exact absurd (exceptMem_dotWal hX') (hOther _ hmem hc hlj go!".wal" walNameP_dotWal)
  subst hjj
  obtain ⟨l1, l2, hcl, -, -⟩ := hOnce
  icases osClaims_agree (L := L) cl (j, NameSet.except X, hj') (by rw [hcl]; simp) hj0 $$ [Hcl Hn] with
    ⟨%h0, Hcl, Hn⟩
  · iframe Hcl Hn
  simp only at h0
  subst h0
  icases walTailsRes_lookupR C Mr s Ls F dir γ tg $$ Htl Htk Hv with ⟨%hlk, Htl, Htk, Hv⟩
  obtain ⟨d', lay', g0, hd', hl', -, htg⟩ := hlk
  rw [hd] at hd'; cases hd'
  rw [hl] at hl'; cases hl'
  icases walGhost_lksAgree s T Lk $$ Hg Htf with ⟨%hlks, Hg, Htf⟩
  have hsn : SegsNamed lay.segs hj0.cur := (HNm dir lay hl).1 hj0 hWDC
  have hnd : (lay.segs.map (·.ino)).Nodup := segsAll_nodup_segs HW.2.2.1 hl
  iframe Hn Htk Hv Htf
  isplitr
  · ipureintro
    refine ⟨⟨d, lay, hd, habs, hsn, hnd, ?_, ?_⟩, hlks⟩ <;> rw [htg] <;> rfl
  isplitl
  · iexists Ls, cl, n, F
    iframe
    ipureintro; exact ⟨Har, HW, HWC, Hab, HNm, Hdko, HAt, Hbd⟩
  · iexact Hk

/-- **`ReleaseLockTo`'s commit** (see the file header). -/
theorem walInv_releaseLks (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (a : w64) (Pre : WalDur → Prop) (Q : WalDur → IProp GF) (ic : Nat) (j : Ino) (X : List GoString)
    (hj0 : NamesH) (γ : GName) (tg : TailG) (γt : GName) (b : Nat) (hcl : tg.2.2.1.length < 2 ^ 64) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      (AU <{ ∃∃ d : WalDur, walDiskAtI (W := W) dir ic d ∗ ⌜Pre d⌝ }> @ walAuMask, ∅
        <{ walDiskAtI (W := W) dir ic { d with unl := max d.unl (walReleasePos (d.H.map WalOpG.toM) a) },
          COMM Q d }>) -∗
      walDirKey (W := W) dir j X -∗ osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj0 -∗
      walTailKey (W := W) dir γ -∗ tailVar (W := W) γ tg -∗
      walTailsFrag (W := W) (<[dir := γt]> (∅ : GMap GoString GName)) (<[dir := b]> (∅ : GMap GoString Nat))
      ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ (∃ d, Q d) ∗
      osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj0 ∗ walTailKey (W := W) dir γ ∗
      tailVar (W := W) γ tg ∗
      ∃ b', walTailsFrag (W := W) (<[dir := γt]> (∅ : GMap GoString GName))
          (<[dir := b']> (∅ : GMap GoString Nat)) ∗
        ⌜b ≤ b' ∧ ∀ (sq ix : Nat) (n : Node), sq < 2 ^ 64 → hj0.cur !! walFileName sq ix = some n →
          uint.nat (W64 ix) < uint.nat a → segStart tg.2.2.1 sq ≤ b'⌝ := by
  iintro #Hinv Hnc Hau #Hk Hn Htk Hv Htf
  imod walInv_open C Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases walInvBody_handleLook C Mr R jr r s dir j X hj0 γ tg _ _ $$ Hb Hk Hn Htk Hv Htf with
    ⟨%hlook, Hb, -, Hn, Htk, Hv, Htf⟩
  obtain ⟨⟨d, lay, hd, habs, hsn, hnd, htH, htc⟩, hlks⟩ := hlook
  obtain ⟨d1, hd1, hbu⟩ := hlks dir b (GMap.lookup_insert_eq _ _ _)
  rw [hd] at hd1; cases hd1
  ihave Hau := atomic_update_mask_weaken walAuMask_sub_top' $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%dc, ⟨Ho, %hpre⟩, Hucl⟩
  unfold walDiskAtI walDirIsI
  icases Ho with ⟨%M, %I, HM, HI, %HMd, %hic⟩
  icases walInvBody_mapLe C Mr R jr r s M $$ Hb HM with ⟨%HMs, Hb, HM⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  obtain ⟨d0, hM0, hle0⟩ := (walOptLe_some_iff _ _).1 HMd
  have hle : walDurLe dc d := by
    have h1 := HMs dir
    rw [hM0, hd] at h1
    obtain ⟨ds, hds, hle1⟩ := (walOptLe_some_iff _ _).1 h1
    cases hds
    exact walDurLe_trans hle0 hle1
  let p := walReleasePos (dc.H.map WalOpG.toM) a
  imod walInvBody_unl C Mr R jr r s dir p M $$ Hb HM with ⟨-, Hb, HM, -⟩
  have hsd' := unlSt_lookup_self s dir p d hd
  imod Hcommit $$ [HM HI] with HQ
  · iexists (unlSt s dir p).wal, I
    iframe HM HI
    ipureintro
    refine ⟨?_, hic⟩
    simp only [hsd', walOptLe]
    exact walDurLe_unl _ hle
  have hb' : max b p ≤ max d.unl p := by omega
  imod walInvBody_lksSet C Mr R jr r (unlSt s dir p) _ _ (<[dir := max b p]> (∅ : GMap GoString Nat))
    (LksOk.single hsd' hb') $$ Hb Htf with ⟨Hb, Htf⟩
  imod Hcl $$ [Hb] with -
  · iexists _; iexact Hb
  imodintro
  iframe Hnc Hn Htk Hv
  isplitl [HQ]
  · iexists dc; iexact HQ
  iexists max b p
  iframe Htf
  ipureintro
  refine ⟨Nat.le_max_left _ _, fun sq ix n hsq hn hia => ?_⟩
  rw [htc]
  have h1 := absD_name_le_releasePos habs hsn hnd hsq (by rw [← htc]; exact hcl) hn hia
  simp only [histM, histN, walReleasePos_normH] at h1
  rw [← hle.1] at h1
  exact Nat.le_trans h1 (Nat.le_max_right _ _)

end iris

end WalFs
end EtcdGrove
end Perennial

end
