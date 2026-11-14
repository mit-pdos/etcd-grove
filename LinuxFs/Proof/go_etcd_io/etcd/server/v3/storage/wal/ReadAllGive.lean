/- Lean-first (no Rocq counterpart).

# `ReadAll`'s handle, the give-back (W3/W5 of `notes/wal-fsext-plan.md`, twenty-seventh session)

What `walOpenWF`'s `walDirH` needs that `ReadAll` holds only as the read's tie (obligation (f)):

* `walNames_last_max` (pure): the tail's name, the last of the directory's sorted `.wal` names, is the
  largest.
* `walInvBody_readGive`: the program's halves of the segments before the tail (the files `ReadAll` read
  and keeps open as locks) given back to the parked state (`walParked_putSegsRes`), so that the record
  of what the handle holds out has only the tail: nothing is in flight (`TailsOnly` with the holder's
  `{dir ↦ γt}` names only this WAL's tail, whose record says none), and, at the same look, the WAL's
  bounds (`WalsBounded`, the WAL being the tail record's) and its key's names (`DirKeysOk`: no `.wal`
  name in `X`).
* `walInv_readGive`: the same at a program step (`notCrashed`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutSync
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenUnpin
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutCommitPure

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **The last of a directory's sorted `.wal` names is the largest.** -/
theorem walNames_last_max {E : Ents} {nm0 : GoString} (hl : (walNames E).getLast? = some nm0) :
    ∀ b n, E !! b = some n → walNameP b = true → b = nm0 ∨ go.GoStringLt b nm0 := by
  intro b n hb hw
  have htr : ∀ a b c : GoString, decide (go.GoStringLt a b ∨ a = b) = true →
      decide (go.GoStringLt b c ∨ b = c) = true → decide (go.GoStringLt a c ∨ a = c) = true := by
    intro a b c h1 h2
    simp only [decide_eq_true_eq] at h1 h2 ⊢
    rcases h1 with h1 | rfl <;> rcases h2 with h2 | rfl
    · exact Or.inl (go.goStringLt_trans h1 h2)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr rfl
  have hto : ∀ a b : GoString,
      (decide (go.GoStringLt a b ∨ a = b) || decide (go.GoStringLt b a ∨ b = a)) = true := by
    intro a b
    by_cases h1 : go.GoStringLt a b
    · simp [h1]
    by_cases h2 : go.GoStringLt b a
    · simp [h2]
    simp [go.goStringLt_eq_of_not_lt h1 h2]
  have hsort : (walNames E).Pairwise (fun a b => decide (go.GoStringLt a b ∨ a = b) = true) :=
    List.pairwise_mergeSort htr hto _
  have hmem := mem_walNames hw hb
  obtain ⟨l, hl'⟩ := List.getLast?_eq_some_iff.1 hl
  rw [hl'] at hmem hsort
  rcases List.mem_append.1 hmem with h | h
  · have := (List.pairwise_append.1 hsort).2.2 b h nm0 (by simp)
    simp only [decide_eq_true_eq] at this
    rcases this with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1
  · simp only [List.mem_singleton] at h
    exact Or.inl h

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The holder's half of the tails' authority bounds what is in flight** (`TailsOnly`). -/
theorem walTailsRes_only (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState) (Ls : GMap GoString WalLay)
    (F : GMap Ino SegFl) (T' : GMap GoString GName) :
    ⊢ walTailsRes (W := W) C Mr s Ls F -∗ walTailsFrag (W := W) T' -∗
      ⌜TailsOnly T' Ls F⌝ ∗ walTailsRes (W := W) C Mr s Ls F ∗ walTailsFrag (W := W) T' := by
  unfold walTailsRes
  iintro ⟨%T, Ha, %Ho, %Hi, Hm, HL⟩ Hf
  icases walTails_agree (W := W) T T' $$ Ha Hf with %hT
  subst hT
  iframe Hf
  isplitr
  · ipureintro; exact Ho
  iexists T
  iframe Ha Hm HL
  ipureintro; exact ⟨Ho, Hi⟩

/-- **The non-tail segments given back** (see the file header). -/
theorem walInvBody_readGive (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (γt : GName) (tg : TailG) (S : List SegG) (o : WalOut)
    (j : Ino) (X : List GoString) (hS : ∀ g ∈ S, g.om.size = g.bs.length)
    (hfl : tg.2.2.2.2.2 = none) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walTailsFrag (W := W) (<[dir := γt]> ∅) -∗
      walTailKey (W := W) dir γt -∗ tailVar (W := W) γt tg -∗ walDirKey (W := W) dir j X -∗
      walOutFrag (W := W) o -∗ ([∗list] g ∈ S, segRes (L := L) g) ==∗
      ⌜(∃ d, s.wal !! dir = some d ∧ d.H = tg.1 ∧ d.metadata = tg.2.1) ∧ WalsBounded s ∧
        (∀ b ∈ X, walNameP b = false)⌝ ∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ walTailsFrag (W := W) (<[dir := γt]> ∅) ∗
      walTailKey (W := W) dir γt ∗ tailVar (W := W) γt tg ∗
      walOutFrag (W := W) ⟨o.O.filter (fun x => decide (x ∉ S.map (·.ino))), o.D, o.T⟩ := by
  iintro Hb Htf Hk Hv #Hkey Ho HS
  iunfold walInvBody at Hb
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, HKa, Hca, %HDK⟩, %HAt, Hnms, %Hbd⟩
  icases walDirKey_lookup (W := W) K dir j X $$ HKa Hkey with %hK
  obtain ⟨-, -, -, -, -, hX, -⟩ := HDK.1 dir j X hK
  icases walTailsRes_lookup (W := W) C Mr s Ls F dir γt tg $$ Htl Hk Hv with ⟨%hlk, Htl, Hk, Hv⟩
  obtain ⟨d, lay, g0, hd, hl, hg0, htg⟩ := hlk
  -- nothing in flight: the holder's tails name only this WAL's, whose record says none
  icases walTailsRes_only (W := W) C Mr s Ls F _ $$ Htl Htf with ⟨%hTO, Htl, Htf⟩
  have hF0 : F = ∅ := by
    refine (GMap.lookup_empty_iff F).1 (fun i => Classical.byContradiction fun hi => ?_)
    obtain ⟨dir', γ', lay', g', hT', hl', hg', hi'⟩ := hTO i hi
    have hdir : dir' = dir := by
      by_cases e : dir' = dir
      · exact e
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm e), GMap.lookup_empty] at hT'; cases hT'
    subst hdir
    rw [hl] at hl'; cases hl'
    rw [hg0] at hg'; cases hg'
    subst hi'
    apply hi
    rw [htg] at hfl
    exact hfl
  subst hF0
  icases (laysResF_empty (L := L) Ls).1 $$ Hlays with Hlays
  icases (laysRes_list (L := L) Ls).1 $$ Hlays with Hlays
  imod walParked_putSegsRes (L := L) (W := W) Ls cl S HW.2.2.1 hS (walsOk_segs_size HW) o $$ Hpk Hlays
    Ho HS with ⟨Hpk, Hlays, Ho⟩
  ihave Hlays := (laysRes_list (L := L) Ls).2 $$ Hlays
  ihave Hlays := (laysResF_empty (L := L) Ls).2 $$ Hlays
  imodintro
  iframe Htf Hk Hv Ho
  isplitr
  · ipureintro
    refine ⟨⟨d, hd, ?_, ?_⟩, Hbd, hX⟩
    · rw [htg]; rfl
    · rw [htg]; rfl
  iunfold walInvBody
  iexists Ls, cl, n, ∅
  iframe Hg Hcl Hcm Hlays HCR Htl Hpk Hnms
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
  ipureintro; exact ⟨HAt, Hbd⟩

/-- **`walInvBody_readGive` at a program step** (`notCrashed`). -/
theorem walInv_readGive (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (γt : GName) (tg : TailG) (S : List SegG) (o : WalOut)
    (j : Ino) (X : List GoString) (hS : ∀ g ∈ S, g.om.size = g.bs.length)
    (hfl : tg.2.2.2.2.2 = none) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walTailsFrag (W := W) (<[dir := γt]> ∅) -∗
      walTailKey (W := W) dir γt -∗ tailVar (W := W) γt tg -∗ walDirKey (W := W) dir j X -∗
      walOutFrag (W := W) o -∗ ([∗list] g ∈ S, segRes (L := L) g) ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗
      ⌜(∃ s d, s.wal !! dir = some d ∧ d.H = tg.1 ∧ d.metadata = tg.2.1 ∧ WalsBounded s) ∧
        (∀ b ∈ X, walNameP b = false)⌝ ∗
      walTailsFrag (W := W) (<[dir := γt]> ∅) ∗
      walTailKey (W := W) dir γt ∗ tailVar (W := W) γt tg ∗
      walOutFrag (W := W) ⟨o.O.filter (fun x => decide (x ∉ S.map (·.ino))), o.D, o.T⟩ := by
  iintro #Hinv Hnc Htf Hk Hv #Hkey Ho HS
  imod walInv_open (L := L) C Mr R jr r ⊤ (fun _ _ => CoPset.mem_full) $$ Hinv Hnc
    with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  imod walInvBody_readGive C Mr R jr r s dir γt tg S o j X hS hfl $$ Hb Htf Hk Hv Hkey Ho HS
    with ⟨%hp, Hb, Htf, Hk, Hv, Ho⟩
  imod Hcl $$ [Hb] with -
  · iexists s; iexact Hb
  imodintro
  iframe Hnc Htf Hk Hv Ho
  ipureintro
  obtain ⟨⟨d, hd, h1, h2⟩, hb, hX⟩ := hp
  exact ⟨⟨s, d, hd, h1, h2, hb⟩, hX⟩

end iris

end WalFs
end EtcdGrove
end Perennial

end
