/- Lean-first (no Rocq counterpart).

# `openAtIndex`'s pin: what `Open` takes out of the parked state (`notes/wal-fsext-plan.md`, W3/W5)

At its pinning step, `Open` (holding the free lock token, `walUnlockedTok`) opens `walInv` and takes the
lock (`walParked_lock`: nothing out, so no change in flight anywhere, `F = ∅`); then, for the WAL in
`dir` (present: `s.wal !! dir = some d`), out of `walParked`:
* the program's halves of its segments from position `k` on (`walParked_takeSegs`), made exact by
  agreement with the invariant's halves (`segRes`: the layout's `OsMeta` and bytes; nothing in
  flight);
* the program's half of the WAL directory's claim (`walParked_takeClaim`), `(lay.j, .except X, hj)`;
* in write mode, the pipeline names' claims (`walParked_takeTmps`).
The holder gets the lock (`walLockedTok`), the record of what it took (`walOutFrag`) and the program's
half of the tails' authority, empty (`walTailsFrag ∅`: no tail registered, so it can put everything
back, `walTailsRes_none`).

* `segsRes_exact`: program halves made exact against the invariant's.
* `walInvBody_pin`: the pin itself (the invariant's contents at the same `s`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailAcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- A resource per element of a list, split at `k`. -/
theorem bigSepL_take_drop {A : Type} (P : A → IProp GF) (S : List A) (k : Nat) :
    ([∗list] x ∈ S, P x) ⊣⊢ ([∗list] x ∈ S.take k, P x) ∗ [∗list] x ∈ S.drop k, P x := by
  conv => lhs; rw [← List.take_append_drop k S]
  exact BigSepL.bigSepL_append

/-- **A segment's program halves made exact** by the invariant's (`segRes`, nothing in flight). -/
theorem segRes_exact (g : SegG) :
    segRes (L := L) g ∗ segResP (L := L) g ⊢ segRes (L := L) g ∗ segRes (L := L) g := by
  unfold segRes segResP
  iintro ⟨⟨Hm, Hb⟩, ⟨%m, %bs, Hm', Hb', %hl⟩⟩
  icases parked_osMeta_agree (L := L) g.ino _ _ g.om m $$ Hm Hm' with %hm
  icases osBytes_agree (L := L) g.ino _ _ 0 g.bs bs hl.symm $$ Hb Hb' with %hb
  subst hm hb
  iframe

/-- The list version of `segRes_exact`. -/
theorem segsRes_exact (S : List SegG) :
    ([∗list] g ∈ S, segRes (L := L) g) ∗ ([∗list] g ∈ S, segResP (L := L) g) ⊢
      ([∗list] g ∈ S, segRes (L := L) g) ∗ [∗list] g ∈ S, segRes (L := L) g := by
  induction S with
  | nil =>
    iintro ⟨H1, -⟩
    iframe H1
    iapply BigSepL.bigSepL_nil.2; iempintro
  | cons g S ih =>
    iintro ⟨H1, H2⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H1 with ⟨Hg, H1⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H2 with ⟨Hg', H2⟩
    icases segRes_exact g $$ [Hg Hg'] with ⟨Hg, Hg'⟩
    · iframe Hg Hg'
    icases ih $$ [H1 H2] with ⟨H1, H2⟩
    · iframe H1 H2
    isplitl [Hg H1]
    · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2; iframe Hg H1
    · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2; iframe Hg' H2

/-- The record of what is out, restated. -/
theorem walOutFrag_eq' {o : WalOut} (o' : WalOut) :
    ⊢@{IProp GF} walOutFrag (W := W) o -∗ ⌜o = o'⌝ -∗ walOutFrag (W := W) o' := by
  iintro Ho %h
  subst h
  iexact Ho

/-- With nothing in flight, a segment's part is its halves. -/
theorem segResF_empty (g : SegG) : segResF (L := L) ∅ g ⊣⊢ segRes (L := L) g := by
  unfold segResF
  rw [GMap.lookup_empty]
  exact .rfl

/-- **`Open`'s pin** (see the file header): the WAL in `dir` present, its segments from position `k`
on, its directory's claim and, in write mode, its pipeline names taken out of the parked state, with
the lock; what the layout says of them. -/
theorem walInvBody_pin (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (d : WalDur) (hd : s.wal !! dir = some d) (k : Nat)
    (write : Bool) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walUnlockedTok (W := W) ==∗
      ∃ (lay : WalLay) (X : List GoString) (hj : NamesH),
        ⌜InArea s.area dir lay.nm ∧ lay.jr = jr ∧ (∀ b ∈ X, walNameP b = false) ∧
          ClaimCoh hj lay.j (.except X) ∧ WalAbsD C Mr d lay hj.cur⌝ ∗
        walInvBody (L := L) (W := W) C Mr R jr r s ∗ walLockedTok (W := W) ∗ walTailsFrag (W := W) ∅ ∗
        walOutFrag (W := W) ⟨(lay.segs.drop k).map (·.ino), [(lay.j, .except X)],
          if write then [dir] else []⟩ ∗
        ([∗list] g ∈ lay.segs.drop k, segRes (L := L) g) ∗
        osNames (L := L) lay.j (.except X) (DFrac.own (1 : Qp).half) hj ∗
        (if write then walTmpsRes (hG := ⟨G, L⟩) lay.j else emp) := by
  iintro Hb Hu
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hn, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    Hdk, %HAt⟩
  obtain ⟨lay, nm, hj, hl, hA, hjr, hnm, hc, habs, hcr⟩ := HW.1 dir d hd
  obtain ⟨X, hX, hcX, hcoh⟩ := hc
  imod walParked_lock (L := L) (W := W) Ls cl F $$ Hpk Hu with ⟨Hpk, Hl, Ho, Htf, %hF⟩
  have hF0 : F = ∅ := (GMap.lookup_empty_iff F).1 hF
  subst hF0
  -- the segments from `k` on
  have hS : ∀ g ∈ lay.segs.drop k, g ∈ segsAll Ls := fun g hg =>
    mem_segsAll hl (List.mem_of_mem_drop hg)
  have hnd : ((lay.segs.drop k).map (·.ino)).Nodup := by
    rw [List.map_drop]
    exact (((segsAll_nodup_iff Ls).1 HW.2.2.1).1 dir lay hl).sublist (List.drop_sublist _ _)
  imod walParked_takeSegs (L := L) (W := W) Ls cl ∅ WalOut.empty (lay.segs.drop k) hS
    (fun _ _ h => by cases h) hnd $$ Hpk Ho with ⟨Hpk, Ho, HS, -⟩
  -- the directory's claim
  imod walParked_takeClaim (L := L) (W := W) Ls cl ∅ _ (lay.j, .except X, hj) hcX
    ⟨dir, lay, hl, rfl, X, rfl, hX⟩ (by simp [WalOut.empty]) $$ Hpk Ho with ⟨Hpk, Ho, Hnm⟩
  -- exact halves
  icases (laysResF_del (L := L) ∅ Ls dir lay hl).1 $$ Hlays with ⟨Hsegs, Hrest⟩
  ihave Hsegs := BigSepL.bigSepL_mono (fun {_ g} _ => (segResF_empty (L := L) g).1) $$ Hsegs
  icases (bigSepL_take_drop (fun g => segRes (L := L) g) lay.segs k).1 $$ Hsegs with ⟨Hpre, Hpost⟩
  icases segsRes_exact (L := L) (lay.segs.drop k) $$ [Hpost HS] with ⟨Hpost, HS⟩
  · iframe Hpost HS
  ihave Hlays := (laysResF_del (L := L) ∅ Ls dir lay hl).2 $$ [Hpre Hpost Hrest]
  · iframe Hrest
    iapply BigSepL.bigSepL_mono (fun {_ g} _ => (segResF_empty (L := L) g).2)
    iapply (bigSepL_take_drop (fun g => segRes (L := L) g) lay.segs k).2
    iframe Hpre Hpost
  have hpure : InArea s.area dir lay.nm ∧ lay.jr = jr ∧ (∀ b ∈ X, walNameP b = false) ∧
      ClaimCoh hj lay.j (.except X) ∧ WalAbsD C Mr d lay hj.cur := by
    rw [hnm]; exact ⟨hA, hjr, hX, hcoh, habs⟩
  cases write with
  | false =>
    imodintro
    iexists lay, X, hj
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe HS Hnm Hl Htf
    isplitr
    · ipureintro; exact hpure
    isplitl [Hg Hcl Hn Hlays HCR Htl Hpk Hdk]
    · iexists Ls, cl, n, ∅
      iframe
      ipureintro; exact ⟨Har, HW, HWC, Hab, HNm, HAt⟩
    · iapply walOutFrag_eq' (W := W) $$ Ho
      ipureintro; simp [WalOut.empty, WalOut.addClaim]
  | true =>
    imod walParked_takeTmps (L := L) (W := W) Ls cl ∅ _ dir lay hl (by simp [WalOut.addClaim, WalOut.empty])
      $$ Hpk Ho with ⟨Hpk, Ho, Ht⟩
    imodintro
    iexists lay, X, hj
    simp only [↓reduceIte]
    iframe HS Hnm Hl Htf Ht
    isplitr
    · ipureintro; exact hpure
    isplitl [Hg Hcl Hn Hlays HCR Htl Hpk Hdk]
    · iexists Ls, cl, n, ∅
      iframe
      ipureintro; exact ⟨Har, HW, HWC, Hab, HNm, HAt⟩
    · iapply walOutFrag_eq' (W := W) $$ Ho
      ipureintro; simp [WalOut.empty, WalOut.addClaim, WalOut.addTmp]

end iris

end WalFs
end EtcdGrove
end Perennial

end
