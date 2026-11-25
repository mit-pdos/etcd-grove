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
* `walNamesRes_lendAt`: with no pending registration, a present WAL's name claim is lent: a fraction of
  `(jr, .only [nm], hn)` holding the WAL's directory, recorded as a loan (returned,
  `walNamesRes_returnName`, before the lock token is: P6b fix A), and a fraction of the area's spine
  (kept), for a read of `r/nm` (`ReadDir.specChildIs`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv

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
    (Wn : List GoString) {s : AbsDiskState} :
    ⊢ walNamesRes (L := L) (W := W) R jr r Ls s -∗ walSplitFrag (W := W) Wn -∗
      walNamesRes (L := L) (W := W) R jr r Ls s ∗ walSplitFrag (W := W) Wn ∗
      ⌜∀ nm ∈ Wn, ∃ dir lay, Ls !! dir = some lay ∧ lay.nm = nm⌝ := by
  iintro Hn Hf
  unfold walNamesRes
  icases Hn with ⟨%o, %Wn', Ha, Hs, %hf, %hun, %hst, Hsp, Hl⟩
  icases walSplit_agree (W := W) Wn' Wn $$ Hs Hf with %he
  subst he
  iframe Hf
  isplitl
  · iexists o, Wn'; iframe; isplitr
    · ipureintro; exact hf
    isplitr
    · ipureintro; exact hun
    ipureintro; exact hst
  ipureintro; exact hf.1

/-- **A present WAL's name claim lent** (see the file header), with no pending registration, the
loan `(nm, q1)` recorded (returned by `walNamesRes_returnName`; the spine's fraction is not counted). -/
theorem walNamesRes_lendAt (R : Roots) (jr : Ino) (r : GoString) (Ls : GMap GoString WalLay)
    (dir : GoString) (lay : WalLay) (nm : GoString) (hl : Ls !! dir = some lay) (hnm : lay.nm = nm)
    (Lo : List (GoString × Qp)) {s : AbsDiskState} :
    ⊢ walNamesRes (L := L) (W := W) R jr r Ls s -∗ walNamesFragS (W := W) ⟨none, none, Lo⟩ ==∗
      walNamesRes (L := L) (W := W) R jr r Ls s ∗
      ∃ (q1 q2 : Qp) (hn : NamesH), walNamesFragS (W := W) ⟨none, none, (nm, q1) :: Lo⟩ ∗
        osNames (L := L) jr (.only [nm]) (DFrac.own q1) hn ∗
        osPathS (L := L) R r (DFrac.own q2) jr ∗
        ⌜NameOk nm ∧ hn.cur !! nm = some (.dir lay.j)⌝ := by
  subst hnm
  iintro Hn Hf
  unfold walNamesRes
  icases Hn with ⟨%o, %Wn, Ha, Hs, %hf, %hun, %hst, ⟨%qs, Hsp⟩, Hl⟩
  icases walNamesS_agree (W := W) o _ $$ Ha Hf with %ho
  subst ho
  have hm : lay.nm ∈ Wn := hf.2 dir lay hl (by simp)
  have hi := idxOf_getElem? hm
  icases BigSepL.bigSepL_lookup_acc_impl hi $$ Hl with ⟨Hn, Hl⟩
  unfold nameShare
  icases Hn with ⟨%q, %hn, Hn, %hq⟩
  obtain ⟨hqv, hnok, hwnm, hcur⟩ := hq
  icases (osNames_frac (L := L) jr (.only [lay.nm]) q.half q.half hn).1 $$ [Hn] with ⟨Hn, Hn2⟩
  · rw [Qp.half_add_half]; iexact Hn
  icases (osPathS_frac (L := L) R r qs.half qs.half jr).1 $$ [Hsp] with ⟨Hsp, Hsp2⟩
  · rw [Qp.half_add_half]; iexact Hsp
  imod walNamesS_set (W := W) _ _ ⟨none, none, (lay.nm, q.half) :: Lo⟩ $$ Ha Hf with ⟨Ha, Hf⟩
  have hqv' : q.half.val + shareLs Wn ((lay.nm, q.half) :: Lo) (Wn.idxOf lay.nm) lay.nm =
      ((1 : Qp).half).val := by
    rw [shareLs_cons_eq]
    have h2 : q.half.val + q.half.val = q.val := congrArg Subtype.val (Qp.half_add_half q)
    rw [← hqv, ← h2]; grind
  imodintro
  isplitr [Hn2 Hsp2 Hf]
  · iexists ⟨none, none, (lay.nm, q.half) :: Lo⟩, Wn
    iframe Ha Hs
    isplitr
    · ipureintro; exact hf
    isplitr
    · ipureintro; exact hun
    isplitr
    · ipureintro
      refine ⟨hst.1, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hm
      · exact hst.2 x hx
    isplitr [Hl Hn]
    · iexists qs.half; iexact Hsp
    iapply Hl $$ [] [Hn]
    · imodintro
      iintro %k %y %hk %hne H
      rw [shareLs_cons_ne Wn Lo lay.nm y q.half k hk hne]
      iexact H
    · iexists q.half, hn
      iframe Hn
      ipureintro; exact ⟨hqv', hnok, hwnm, hcur⟩
  iexists q.half, qs.half, hn
  iframe Hn2 Hsp2 Hf
  ipureintro; exact ⟨hnok, hcur dir lay hl rfl⟩

/-- **A lent fraction of a name claim returned** (`walNamesRes_lendAt`'s, `ReadAll`'s). -/
theorem walNamesRes_returnName (R : Roots) (jr : Ino) (r : GoString) (Ls : GMap GoString WalLay)
    (nm : GoString) (q : Qp) (hn' : NamesH) (Lo : List (GoString × Qp)) (hx : (nm, q) ∈ Lo)
    {s : AbsDiskState} :
    ⊢ walNamesRes (L := L) (W := W) R jr r Ls s -∗ walNamesFragS (W := W) ⟨none, none, Lo⟩ -∗
      osNames (L := L) jr (.only [nm]) (DFrac.own q) hn' ==∗
      walNamesRes (L := L) (W := W) R jr r Ls s ∗ walNamesFragS (W := W) ⟨none, none, Lo.erase (nm, q)⟩ := by
  iintro Hn Hf Hn'
  unfold walNamesRes
  icases Hn with ⟨%o, %Wn, Ha, Hs, %hf, %hun, %hst, Hsp, Hl⟩
  icases walNamesS_agree (W := W) o _ $$ Ha Hf with %ho
  subst ho
  have hm : nm ∈ Wn := hst.2 _ hx
  have hi := idxOf_getElem? hm
  have hperm : Lo.Perm ((nm, q) :: Lo.erase (nm, q)) := List.perm_cons_erase hx
  icases BigSepL.bigSepL_lookup_acc_impl hi $$ Hl with ⟨Hn, Hl⟩
  unfold nameShare
  icases Hn with ⟨%q0, %hn, Hn, %hq⟩
  obtain ⟨hqv, hnok, hwnm, hcur⟩ := hq
  icases osNames_agree (L := L) jr (.only [nm]) _ _ hn' hn $$ Hn' Hn with %e1
  subst e1
  ihave Hn := (osNames_frac (L := L) jr (.only [nm]) q0 q hn').2 $$ [Hn Hn']
  · iframe
  imod walNamesS_set (W := W) _ _ ⟨none, none, Lo.erase (nm, q)⟩ $$ Ha Hf with ⟨Ha, Hf⟩
  have hqv' : (q0 + q).val + shareLs Wn (Lo.erase (nm, q)) (Wn.idxOf nm) nm = ((1 : Qp).half).val := by
    rw [shareLs_perm Wn hperm, shareLs_cons_eq] at hqv
    have h3 : (q0 + q).val = q0.val + q.val := rfl
    rw [h3, ← hqv]; grind
  imodintro
  iframe Hf
  iexists ⟨none, none, Lo.erase (nm, q)⟩, Wn
  iframe Ha Hs Hsp
  isplitr
  · ipureintro; exact hf
  isplitr
  · ipureintro; exact hun
  isplitr
  · ipureintro; exact ⟨hst.1, fun x hx' => hst.2 x (List.mem_of_mem_erase hx')⟩
  iapply Hl $$ [] [Hn]
  · imodintro
    iintro %k %y %hk %hne H
    rw [shareLs_perm Wn hperm, shareLs_cons_ne Wn _ nm y q k hk hne]
    iexact H
  · iexists q0 + q, hn'
    iframe Hn
    ipureintro; exact ⟨hqv', hnok, hwnm, hcur⟩

/-- `walNamesRes_returnName` of the last loan out, back to no loan (`walNamesFrag none`). -/
theorem walNamesRes_returnName0 (R : Roots) (jr : Ino) (r : GoString) (Ls : GMap GoString WalLay)
    (nm : GoString) (q : Qp) (hn' : NamesH) {s : AbsDiskState} :
    ⊢ walNamesRes (L := L) (W := W) R jr r Ls s -∗ walNamesFragS (W := W) ⟨none, none, [(nm, q)]⟩ -∗
      osNames (L := L) jr (.only [nm]) (DFrac.own q) hn' ==∗
      walNamesRes (L := L) (W := W) R jr r Ls s ∗ walNamesFrag (W := W) none := by
  iintro Hn Hf Hn'
  imod walNamesRes_returnName R jr r Ls nm q hn' [(nm, q)] (by simp) $$ Hn Hf Hn' with ⟨Hn, Hf⟩
  imodintro
  iframe Hn
  unfold walNamesFrag
  simp only [List.erase_cons_head]
  iexact Hf

end iris

end WalFs
end EtcdGrove
end Perennial

end
