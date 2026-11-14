/- Lean-first (no Rocq counterpart).

# The split WAL names, as the program's area part sees them (G-spine; `notes/wal-fsext-plan.md`,
W1 log, fourteenth session)

`walAreaRes` holds the program's half of the area claim on names `N` and the split names `Wn`
(`walSplitFrag Wn`, the invariant's `walNamesRes` the other half): every WAL name is in `N` or split
(registered: its own claim `.only [nm]`, `nameShare`). A split name is a present WAL's, and with the
lock's `walNamesFrag none` every present WAL's name is split. So:

* `split_absent`: with no WAL at `dir = r/nm`, `nm` is not split (so `N` holds it: the area claim's
  history says `nm` is absent, as before the split);
* `walNamesRes_splitOk`: the agreement, and the split names' facts;
* `walNamesRes_lendAt`: with `walNamesFrag none`, a present WAL's name claim is lent: a fraction of
  `(jr, .only [nm], hn)` holding the WAL's directory and a fraction of the area's spine (both kept by
  the borrower, never returned), for a read of `r/nm` (`ReadDir.specChildIs`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **A split name is a present WAL's**: with no WAL at `dir`, its name is not split. -/
theorem split_absent {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {Wn : List GoString} {dir nm : GoString}
    (hok : WalsOk C Mr R jr s Ls cl n)
    (hW : ∀ nm ∈ Wn, ∃ dir lay, Ls !! dir = some lay ∧ lay.nm = nm)
    (hin : InArea s.area dir nm) (hsd : s.wal !! dir = none) : nm ∉ Wn := by
  intro hm
  obtain ⟨dir', lay, hl, hnm⟩ := hW nm hm
  obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir' = some d := by
    cases h' : s.wal !! dir' with
    | none => rw [hok.2.1 dir' h'] at hl; cases hl
    | some d => exact ⟨d, rfl⟩
  obtain ⟨l2, nm2, -, hl2, hin2, -, hnm2, -⟩ := hok.1 dir' d hd
  rw [hl] at hl2; cases hl2
  have e : dir' = dir := by rw [hin2.2, hin.2, ← hnm2, hnm]
  subst e
  rw [hd] at hsd; cases hsd

/-- **With no pending registration, a present WAL's name is split**, and the WAL's layout is named
`nm`. -/
theorem split_present {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {Wn : List GoString} {dir nm : GoString}
    {d : WalDur} (hok : WalsOk C Mr R jr s Ls cl n)
    (hW : ∀ dir lay, Ls !! dir = some lay → (none : Option GoString) ≠ some dir → lay.nm ∈ Wn)
    (hin : InArea s.area dir nm) (hsd : s.wal !! dir = some d) :
    nm ∈ Wn ∧ ∃ lay, Ls !! dir = some lay ∧ lay.nm = nm := by
  obtain ⟨lay, nm2, -, hl, hin2, -, hnm2, -⟩ := hok.1 dir d hsd
  have e : nm2 = nm := List.append_cancel_left (hin2.2.symm.trans hin.2)
  subst e
  exact ⟨hnm2 ▸ hW dir lay hl (by simp), lay, hl, hnm2⟩

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The program's split names agree with the invariant's**, and are present WALs' names. -/
theorem walNamesRes_splitOk (R : Roots) (jr : Ino) (r : GoString) (Ls : GMap GoString WalLay)
    (Wn : List GoString) :
    ⊢ walNamesRes (L := L) (W := W) R jr r Ls -∗ walSplitFrag (W := W) Wn -∗
      walNamesRes (L := L) (W := W) R jr r Ls ∗ walSplitFrag (W := W) Wn ∗
      ⌜∀ nm ∈ Wn, ∃ dir lay, Ls !! dir = some lay ∧ lay.nm = nm⌝ := by
  iintro Hn Hf
  unfold walNamesRes
  icases Hn with ⟨%o, %Wn', Ha, Hs, %hf, Hsp, Hl⟩
  icases walSplit_agree (W := W) Wn' Wn $$ Hs Hf with %he
  subst he
  iframe Hf
  isplitl
  · iexists o, Wn'; iframe; ipureintro; exact hf
  ipureintro; exact hf.1

/-- **A present WAL's name claim lent** (see the file header), with no pending registration. -/
theorem walNamesRes_lendAt (R : Roots) (jr : Ino) (r : GoString) (Ls : GMap GoString WalLay)
    (dir : GoString) (lay : WalLay) (nm : GoString) (hl : Ls !! dir = some lay) (hnm : lay.nm = nm) :
    ⊢ walNamesRes (L := L) (W := W) R jr r Ls -∗ walNamesFrag (W := W) none -∗
      walNamesRes (L := L) (W := W) R jr r Ls ∗ walNamesFrag (W := W) none ∗
      ∃ (q1 q2 : Qp) (hn : NamesH), osNames (L := L) jr (.only [nm]) (DFrac.own q1) hn ∗
        osPathS (L := L) R r (DFrac.own q2) jr ∗
        ⌜NameOk nm ∧ hn.cur !! nm = some (.dir lay.j)⌝ := by
  subst hnm
  iintro Hn Hf
  unfold walNamesRes
  icases Hn with ⟨%o, %Wn, Ha, Hs, %hf, ⟨%qs, Hsp⟩, Hl⟩
  icases walNames_agree (W := W) o none $$ Ha Hf with %ho
  subst ho
  have hm : lay.nm ∈ Wn := hf.2 dir lay hl (by simp)
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
  icases (BigSepL.bigSepL_lookup_acc hi).1 $$ Hl with ⟨Hn, Hl⟩
  unfold nameShare
  icases Hn with ⟨%q, %hn, Hn, %hq⟩
  obtain ⟨hnok, hwnm, hcur⟩ := hq
  icases (osNames_frac (L := L) jr (.only [lay.nm]) q.half q.half hn).1 $$ [Hn] with ⟨Hn, Hn2⟩
  · rw [Qp.half_add_half]; iexact Hn
  icases (osPathS_frac (L := L) R r qs.half qs.half jr).1 $$ [Hsp] with ⟨Hsp, Hsp2⟩
  · rw [Qp.half_add_half]; iexact Hsp
  have hset : Wn.set i lay.nm = Wn := by
    obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp hi
    rw [← he]; exact List.set_getElem_self hlt
  iframe Hf
  isplitr [Hn2 Hsp2]
  · iexists none, Wn
    iframe Ha Hs
    isplitr
    · ipureintro; exact hf
    isplitr [Hl Hn]
    · iexists qs.half; iexact Hsp
    ispecialize Hl $$ %(lay.nm)
    rw [hset]
    iapply Hl
    iexists q.half, hn
    iframe Hn
    ipureintro; exact ⟨hnok, hwnm, hcur⟩
  iexists q.half, qs.half, hn
  iframe Hn2 Hsp2
  ipureintro; exact ⟨hnok, hcur dir lay hl rfl⟩

end iris

end WalFs
end EtcdGrove
end Perennial

end
