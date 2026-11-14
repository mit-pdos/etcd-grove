/- Lean-first (no Rocq counterpart).

# `openAtIndex`'s put-back: what a failing `Open` returns to the parked state (`notes/wal-fsext-plan.md`, W3/W5)

After its pin (`walInvBody_pin`, `OpenPinTake.lean`), an `Open` that fails (`selectWALFiles`'
errors, `openWALFiles`' `EMFILE`/`EIO`, ...) gives everything back at a later step and releases the
lock (`walInvBody_unpin`): the program's halves of the segments it took (by inode, onto whatever
segment of the layouts now has that inode, `walParked_putSegIno`), the WAL directory's claim (found
once among the invariant's claims through the WAL's key, `walDirKey`, and `DirKeysOk`: gap C), and in
write mode the pipeline names' claims (at the key's directory). Nothing is in flight: the holder's
half of the tails' authority is empty (`walTailsRes_none`).

* `segRes_meta`/`segsRes_meta`: the invariant's segment halves agree with a held `OsMeta` half.
* `walsOk_segs_size`: every segment's size is its bytes' (`WalAbsD.metas`).
* `walParked_putSegsRes`: the put-back of a list of exact halves.
* `walInvBody_unpin`: the body-level put-back with the lock released.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenPinTake
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ParkedPut

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- Every named segment's size is its bytes' (`WalAbsD.metas`). -/
theorem walsOk_segs_size {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} (h : WalsOk C Mr R jr s Ls cl n) :
    ∀ g ∈ segsAll Ls, g.om.size = g.bs.length := by
  intro g hg
  obtain ⟨dir, lay, hl, hg'⟩ := segsAll_mem hg
  obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir = some d := by
    cases e : s.wal !! dir with
    | none => rw [h.2.1 dir e] at hl; cases hl
    | some d => exact ⟨d, rfl⟩
  obtain ⟨lay', nm, hj, hl', -, -, -, -, habs, -⟩ := h.1 dir d hd
  rw [hl] at hl'; cases hl'
  exact (habs.metas g hg').1

theorem filter_del_cons (l L : List Ino) (i : Ino) :
    (l.filter (· ≠ i)).filter (fun x => decide (x ∉ L)) = l.filter (fun x => decide (x ∉ i :: L)) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  by_cases h1 : x = i <;> by_cases h2 : x ∈ L <;> simp [h1, h2]

theorem filter_not_mem_self (l : List Ino) : l.filter (fun x => decide (x ∉ l)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx; simp [hx]

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- A segment's invariant halves agree with a held `OsMeta` part of its inode. -/
theorem segRes_meta (g : SegG) (i : Ino) (dq : DFrac) (m : OsMeta) :
    segRes (L := L) g ∗ osMeta (L := L) i dq m ⊢
      ⌜g.ino = i → g.om = m⌝ ∗ segRes (L := L) g ∗ osMeta (L := L) i dq m := by
  by_cases e : g.ino = i
  · subst e
    unfold segRes
    iintro ⟨⟨Hg, Hb⟩, Hm⟩
    icases parked_osMeta_agree (L := L) g.ino _ _ g.om m $$ Hg Hm with %h
    iframe Hg Hb Hm
    ipureintro; exact fun _ => h
  · iintro ⟨Hg, Hm⟩
    iframe Hg Hm
    ipureintro; exact fun h => absurd h e

/-- The list version of `segRes_meta`. -/
theorem segsRes_meta (S : List SegG) (i : Ino) (dq : DFrac) (m : OsMeta) :
    ([∗list] g ∈ S, segRes (L := L) g) ∗ osMeta (L := L) i dq m ⊢
      ⌜∀ g ∈ S, g.ino = i → g.om = m⌝ ∗ ([∗list] g ∈ S, segRes (L := L) g) ∗ osMeta (L := L) i dq m := by
  induction S with
  | nil =>
    iintro ⟨H, Hm⟩
    iframe H Hm
    ipureintro; simp
  | cons g S ih =>
    iintro ⟨H, Hm⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H with ⟨Hg, H⟩
    icases segRes_meta g i dq m $$ [Hg Hm] with ⟨%h1, Hg, Hm⟩
    · iframe Hg Hm
    icases ih $$ [H Hm] with ⟨%h2, H, Hm⟩
    · iframe H Hm
    iframe Hm
    isplitr
    · ipureintro
      intro g' hg'
      rcases List.mem_cons.1 hg' with rfl | hg'
      · exact h1
      · exact h2 g' hg'
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    iframe Hg H

/-- **Exact halves of segments put back by inode** (`walParked_putSegIno` for each), nothing in flight:
every segment of the layouts and of `S` of its bytes' size, so that a layout's segment with the inode
of one of `S` has its length (by the `OsMeta` agreement with the invariant's halves). -/
theorem walParked_putSegsRes (Ls : GMap GoString WalLay) (cl : List Claim) (S : List SegG)
    (hnd : ((segsAll Ls).map (·.ino)).Nodup) (hS : ∀ g ∈ S, g.om.size = g.bs.length)
    (hsz : ∀ g ∈ segsAll Ls, g.om.size = g.bs.length) :
    ∀ o : WalOut, ⊢ walParked (L := L) (W := W) Ls cl ∅ -∗
      ([∗list] g ∈ segsAll Ls, segRes (L := L) g) -∗ walOutFrag (W := W) o -∗
      ([∗list] g ∈ S, segRes (L := L) g) ==∗
      walParked (L := L) (W := W) Ls cl ∅ ∗ ([∗list] g ∈ segsAll Ls, segRes (L := L) g) ∗
        walOutFrag (W := W) ⟨o.O.filter (fun x => decide (x ∉ S.map (·.ino))), o.D, o.T⟩ := by
  induction S with
  | nil =>
    intro o
    iintro Hp Hi Ho -
    iframe Hp Hi
    iapply walOutFrag_eq' (W := W) $$ Ho
    ipureintro; cases o
    simp only [List.map_nil, WalOut.mk.injEq, and_true]
    exact (List.filter_eq_self.2 (fun _ _ => by simp)).symm
  | cons g S ih =>
    intro o
    iintro Hp Hi Ho HS
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ HS with ⟨Hg, HS⟩
    iunfold segRes at Hg
    icases Hg with ⟨Hgm, Hgb⟩
    icases segsRes_meta (segsAll Ls) g.ino _ g.om $$ [Hi Hgm] with ⟨%hm, Hi, Hgm⟩
    · iframe Hi Hgm
    have hlen : ∀ g' ∈ segsAll Ls, g'.ino = g.ino → g'.bs.length = g.bs.length := fun g' hg' hi => by
      rw [← hsz g' hg', hm g' hg' hi, hS g (List.mem_cons_self ..)]
    imod walParked_putSegIno (L := L) (W := W) Ls cl ∅ o g hnd (GMap.lookup_empty _) hlen $$ Hp Ho
      [Hgm Hgb] with ⟨Hp, Ho⟩
    · iapply segRes_segResP (L := L) g
      unfold segRes; iframe Hgm Hgb
    imod ih (fun g' hg' => hS g' (List.mem_cons_of_mem _ hg')) (o.delSeg g.ino) $$ Hp Hi Ho HS
      with ⟨Hp, Hi, Ho⟩
    imodintro
    iframe Hp Hi
    iapply walOutFrag_eq' (W := W) $$ Ho
    ipureintro
    simp only [WalOut.delSeg, List.map_cons]
    rw [filter_del_cons]

/-- **`Open`'s put-back** (see the file header): at the invariant's contents at any `s`, the lock,
the holder's empty half of the tails' authority, its record of what it took (the segments `S`, the WAL
directory's claim `(j, .except X)`, the pipeline names of `dir` in write mode), the exact halves of `S`
(each of its bytes' size, the inodes distinct), the claim's half, the pipeline names' claims in write
mode and the WAL's key: the contents at `s` and the free lock token. -/
theorem walInvBody_unpin (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (S : List SegG)
    (write : Bool) (hS : ∀ g ∈ S, g.om.size = g.bs.length) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walLockedTok (W := W) -∗ walTailsFrag (W := W) ∅ -∗
      walOutFrag (W := W) ⟨S.map (·.ino), [(j, .except X)], if write then [dir] else []⟩ -∗
      ([∗list] g ∈ S, segRes (L := L) g) -∗ osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj -∗
      (if write then walTmpsRes (hG := ⟨G, L⟩) j else emp) -∗ walDirKey (W := W) dir j X ==∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ walUnlockedTok (W := W) := by
  iintro Hb Hl Htf Ho HS Hn Ht #Hk
  iunfold walInvBody at Hb
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, HKa, Hca, %HDK⟩, %HAt⟩
  icases walTailsRes_none (W := W) C Mr s Ls F $$ Htl Htf with ⟨%hF, Htl, Htf⟩
  have hF0 : F = ∅ := (GMap.lookup_empty_iff F).1 hF
  subst hF0
  icases walDirKey_lookup (W := W) K dir j X $$ HKa Hk with %hK
  obtain ⟨lay', hj', hl', hlj', hjr', hX', honce', hcoh', hex'⟩ := HDK.1 dir j X hK
  subst hlj'
  have hD : DirClaimOk jr cl lay'.j X hj' := ⟨hjr', hX', honce', hcoh', hex'⟩
  obtain ⟨l1, l2, hcl, hkey⟩ := hD.key_once
  -- the claim's history: the invariant's half agrees with the held one
  have hmem : ((lay'.j, NameSet.except X, hj'), DFrac.own (1 : Qp).half) ∈
      cl.map (fun c => (c, DFrac.own (1 : Qp).half)) := by
    rw [hcl]; exact List.mem_map_of_mem (by simp)
  unfold osClaims
  icases (BigSepL.bigSepL_mem_acc hmem) $$ Hcl with ⟨Hi, Hcl⟩
  icases osNames_agree (L := L) lay'.j (NameSet.except X) _ _ hj hj' $$ Hn Hi with %he
  subst he
  ihave Hcl := Hcl $$ Hi
  -- the segments
  icases (laysResF_empty (L := L) Ls).1 $$ Hlays with Hlays
  icases (laysRes_list (L := L) Ls).1 $$ Hlays with Hlays
  imod walParked_putSegsRes (L := L) (W := W) Ls cl S HW.2.2.1 hS (walsOk_segs_size HW) _ $$ Hpk Hlays
    Ho HS with ⟨Hpk, Hlays, Ho⟩
  rw [filter_not_mem_self]
  -- the claim
  rw [hcl] at HW HWC ⊢
  imod walParked_putClaim (L := L) (W := W) Ls l1 l2 ∅ _ (lay'.j, NameSet.except X, hj) hkey $$ Hpk Ho Hn
    with ⟨Hpk, Ho⟩
  -- the pipeline names, then the lock
  have hkill : ∀ (T : List GoString), ⊢ walParked (L := L) (W := W) Ls (l1 ++ (lay'.j, NameSet.except X, hj) :: l2) ∅ -∗
      walOutFrag (W := W) (WalOut.delClaim ⟨[], [(lay'.j, NameSet.except X)], T⟩
        ((lay'.j, NameSet.except X, hj).1, (lay'.j, NameSet.except X, hj).2.1)) -∗
      ⌜T = []⌝ -∗ walLockedTok (W := W) -∗ walTailsFrag (W := W) ∅ ==∗
      walParked (L := L) (W := W) Ls (l1 ++ (lay'.j, NameSet.except X, hj) :: l2) ∅ ∗
        walUnlockedTok (W := W) := by
    intro T
    iintro Hpk Ho %hT Hl Htf
    subst hT
    iapply walParked_unlock (L := L) (W := W) Ls _ ∅ $$ Hpk Hl [Ho] Htf
    iapply walOutFrag_eq' (W := W) $$ Ho
    ipureintro; simp [WalOut.delClaim, WalOut.empty]
  have hclose : ⊢ walParked (L := L) (W := W) Ls (l1 ++ (lay'.j, NameSet.except X, hj) :: l2) ∅ -∗
      walUnlockedTok (W := W) -∗ walGhost (W := W) s -∗
      osClaims L ((l1 ++ (lay'.j, NameSet.except X, hj) :: l2).map
        (fun c => (c, DFrac.own (1 : Qp).half))) -∗ osCommitLb (L := L) n -∗
      ([∗list] g ∈ segsAll Ls, segRes (L := L) g) -∗
      (∃ CR, walCreatingAuth (W := W) CR ∗ ⌜CreatingOk jr (l1 ++ (lay'.j, NameSet.except X, hj) :: l2) CR⌝) -∗
      walTailsRes (W := W) C Mr s Ls ∅ -∗ walDirKeysAuth (W := W) K -∗ walCutAuth (W := W) cp -∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ walUnlockedTok (W := W) := by
    rw [hcl] at HDK HAt HNm Hab
    iintro Hpk Hu Hg Hcl Hcm Hlays HCR Htl HKa Hca
    iframe Hu
    unfold walInvBody
    iexists Ls, (l1 ++ (lay'.j, NameSet.except X, hj) :: l2), n, ∅
    ihave Hlays := (laysRes_list (L := L) Ls).2 $$ Hlays
    ihave Hlays := (laysResF_empty (L := L) Ls).2 $$ Hlays
    iframe Hg Hcl Hcm HCR Htl Hpk Hlays
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
    isplitl [HKa Hca]
    · iexists K, cp
      iframe HKa Hca
      ipureintro; exact HDK
    ipureintro; exact HAt
  unfold osClaims at hclose
  cases write with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    imod hkill [] $$ Hpk Ho [] Hl Htf with ⟨Hpk, Hu⟩
    · ipureintro; rfl
    imodintro
    iapply hclose $$ Hpk Hu Hg Hcl Hcm Hlays HCR Htl HKa Hca
  | true =>
    simp only [↓reduceIte]
    imod walParked_putTmps (L := L) (W := W) Ls _ ∅ _ dir lay' hl' $$ Hpk Ho Ht with ⟨Hpk, Ho⟩
    imod hkill [] $$ Hpk [Ho] [] Hl Htf with ⟨Hpk, Hu⟩
    · iapply walOutFrag_eq' (W := W) $$ Ho
      ipureintro; simp [WalOut.delTmp, WalOut.delClaim]
    · ipureintro; rfl
    imodintro
    iapply hclose $$ Hpk Hu Hg Hcl Hcm Hlays HCR Htl HKa Hca

end iris

end WalFs
end EtcdGrove
end Perennial

end
