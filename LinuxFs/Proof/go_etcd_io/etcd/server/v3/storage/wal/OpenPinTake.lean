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

section pure
variable [GooseExts]

/-- **A WAL keyed** (its directory claim's facts, `DirClaimsOk`'s), the directory without a key. -/
theorem dirKeysOk_key {C : WalCodec} {Mr : WalMarshal} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {K : GMap GoString (Ino × List GoString)}
    {cp : Option GoString} {dir : GoString} {lay : WalLay} {X : List GoString} {hj : NamesH}
    (h : DirKeysOk C Mr jr s Ls cl n K cp) (hl : Ls !! dir = some lay) (hD : DirClaimOk jr cl lay.j X hj) :
    DirKeysOk C Mr jr s Ls cl n (<[dir := (lay.j, X)]> K) cp := by
  refine ⟨fun dir' j X' hk => ?_, h.2.1, h.2.2⟩
  by_cases e : dir' = dir
  · subst e
    rw [GMap.lookup_insert_eq] at hk
    simp only [Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    exact ⟨lay, hj, hl, rfl, hD⟩
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hk
    exact h.1 dir' j X' hk

end pure

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

/-- **The pinned WAL's key** (`walDirKey`): the generation's (`walDirKeysAuth_get`) if it has one, else
made (`walDirKey_insert`, `dirKeysOk_key`); its claim the WAL directory's (`DirClaimsOk`, gap C). -/
theorem walDirKeys_pin (C : WalCodec) (Mr : WalMarshal) (jr : Ino) (s : AbsDiskState)
    (Ls : GMap GoString WalLay) (cl : List Claim) (n : Nat) (K : GMap GoString (Ino × List GoString))
    (cp : Option GoString) (dir : GoString) (lay : WalLay) (X : List GoString) (hj : NamesH)
    (hK : DirKeysOk C Mr jr s Ls cl n K cp) (hl : Ls !! dir = some lay)
    (hX : ∀ b ∈ X, walNameP b = false) (hc : (lay.j, NameSet.except X, hj) ∈ cl) :
    ⊢ walDirKeysAuth (W := W) K ==∗ ∃ K', walDirKeysAuth (W := W) K' ∗
      ⌜DirKeysOk C Mr jr s Ls cl n K' cp⌝ ∗ walDirKey (W := W) dir lay.j X := by
  iintro Ha
  cases e : K !! dir with
  | none =>
    obtain ⟨X2, hj2, hD⟩ := hK.2.2 dir lay hl
    obtain ⟨hXe, hje⟩ := hD.eq_of_mem hX hc
    subst hXe hje
    imod walDirKey_insert (W := W) K dir lay.j X e $$ Ha with ⟨Ha, Hk⟩
    imodintro
    iexists _
    iframe Ha Hk
    ipureintro; exact dirKeysOk_key hK hl hD
  | some x =>
    obtain ⟨j', X'⟩ := x
    obtain ⟨lay1, hj1, hl1, hlj, hjr, hX1, ho, hco, hex⟩ := hK.1 dir j' X' e
    rw [hl] at hl1
    cases hl1
    subst hlj
    obtain ⟨hXe, -⟩ := DirClaimOk.eq_of_mem (jr := jr) ⟨hjr, hX1, ho, hco, hex⟩ hX hc
    subst hXe
    icases walDirKeysAuth_get (W := W) K dir lay.j X e $$ Ha with ⟨Ha, Hk⟩
    imodintro
    iexists K
    iframe Ha Hk
    ipureintro; exact hK

/-- **`Open`'s pin** (see the file header): the WAL in `dir` present, its segments from position `k lay` (a function of the layout: `selectWALFiles`' `walSearch`)
on, its directory's claim and, in write mode, its pipeline names taken out of the parked state, with
the lock; what the layout says of them. -/
theorem walInvBody_pin (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (d : WalDur) (hd : s.wal !! dir = some d) (k : WalLay → Nat)
    (write : Bool) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walUnlockedTok (W := W) ==∗
      ∃ (lay : WalLay) (X : List GoString) (hj : NamesH),
        ⌜InArea s.area dir lay.nm ∧ lay.jr = jr ∧ (∀ b ∈ X, walNameP b = false) ∧
          ClaimCoh hj lay.j (.except X) ∧ WalAbsD C Mr d lay hj.cur ∧
          (lay.segs.map (·.ino)).Nodup ∧ SegsNamed lay.segs hj.cur⌝ ∗ walDirKey (W := W) dir lay.j X ∗
        walInvBody (L := L) (W := W) C Mr R jr r s ∗ walLockedTok (W := W) ∗ walTailsFrag (W := W) ∅ ∗
        walOutFrag (W := W) ⟨(lay.segs.drop (k lay)).map (·.ino), [(lay.j, .except X)],
          if write then [dir] else []⟩ ∗
        ([∗list] g ∈ lay.segs.drop (k lay), segRes (L := L) g) ∗
        osNames (L := L) lay.j (.except X) (DFrac.own (1 : Qp).half) hj ∗
        (if write then walTmpsRes (hG := ⟨G, L⟩) lay.j else emp) := by
  iintro Hb Hu
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hn, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    Hdk, %HAt⟩
  obtain ⟨lay, nm, hj, hl, hA, hjr, hnm, hc, habs, hcr⟩ := HW.1 dir d hd
  obtain ⟨X, hX, hcX, hcoh⟩ := hc
  icases Hdk with ⟨%K, %cp, HKa, Hca, %HDK⟩
  imod walDirKeys_pin C Mr jr s Ls cl n K cp dir lay X hj HDK hl hX hcX $$ HKa with ⟨%K', HKa, %HDK', #Hkey⟩
  imod walParked_lock (L := L) (W := W) Ls cl F $$ Hpk Hu with ⟨Hpk, Hl, Ho, Htf, %hF⟩
  have hF0 : F = ∅ := (GMap.lookup_empty_iff F).1 hF
  subst hF0
  -- the segments from `k` on
  have hS : ∀ g ∈ lay.segs.drop (k lay), g ∈ segsAll Ls := fun g hg =>
    mem_segsAll hl (List.mem_of_mem_drop hg)
  have hnd : ((lay.segs.drop (k lay)).map (·.ino)).Nodup := by
    rw [List.map_drop]
    exact (((segsAll_nodup_iff Ls).1 HW.2.2.1).1 dir lay hl).sublist (List.drop_sublist _ _)
  imod walParked_takeSegs (L := L) (W := W) Ls cl ∅ WalOut.empty (lay.segs.drop (k lay)) hS
    (fun _ _ h => by cases h) hnd $$ Hpk Ho with ⟨Hpk, Ho, HS, -⟩
  -- the directory's claim
  imod walParked_takeClaim (L := L) (W := W) Ls cl ∅ _ (lay.j, .except X, hj) hcX
    ⟨dir, lay, hl, rfl, X, rfl, hX⟩ (by simp [WalOut.empty]) $$ Hpk Ho with ⟨Hpk, Ho, Hnm⟩
  -- exact halves
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
      ClaimCoh hj lay.j (.except X) ∧ WalAbsD C Mr d lay hj.cur ∧ (lay.segs.map (·.ino)).Nodup ∧
      SegsNamed lay.segs hj.cur := by
    rw [hnm]
    exact ⟨hA, hjr, hX, hcoh, habs, ((segsAll_nodup_iff Ls).1 HW.2.2.1).1 dir lay hl,
      (HNm dir lay hl).1 hj ⟨X, hX, hcX, hcoh⟩⟩
  cases write with
  | false =>
    imodintro
    iexists lay, X, hj
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe HS Hnm Hl Htf Hkey
    isplitr
    · ipureintro; exact hpure
    isplitl [Hg Hcl Hn Hlays HCR Htl Hpk HKa Hca]
    · iexists Ls, cl, n, ∅
      iframe
      ipureintro; exact ⟨Har, HW, HWC, Hab, HNm, HDK', HAt⟩
    · iapply walOutFrag_eq' (W := W) $$ Ho
      ipureintro; simp [WalOut.empty, WalOut.addClaim]
  | true =>
    imod walParked_takeTmps (L := L) (W := W) Ls cl ∅ _ dir lay hl (by simp [WalOut.addClaim, WalOut.empty])
      $$ Hpk Ho with ⟨Hpk, Ho, Ht⟩
    imodintro
    iexists lay, X, hj
    simp only [↓reduceIte]
    iframe HS Hnm Hl Htf Ht Hkey
    isplitr
    · ipureintro; exact hpure
    isplitl [Hg Hcl Hn Hlays HCR Htl Hpk HKa Hca]
    · iexists Ls, cl, n, ∅
      iframe
      ipureintro; exact ⟨Har, HW, HWC, Hab, HNm, HDK', HAt⟩
    · iapply walOutFrag_eq' (W := W) $$ Ho
      ipureintro; simp [WalOut.empty, WalOut.addClaim, WalOut.addTmp]

end iris

end WalFs
end EtcdGrove
end Perennial

end
