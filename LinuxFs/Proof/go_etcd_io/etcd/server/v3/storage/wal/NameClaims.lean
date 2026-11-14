/- Lean-first (no Rocq counterpart).

# Paths to a WAL directory (G-spine; `notes/wal-fsext-plan.md`, W1 log, thirteenth session)

A path to `dir = r/nm` is a spine through a fraction of a claim on `nm` alone. The invariant keeps,
for every registered WAL name, a fraction of the program's half of its own claim `(jr, .only [nm])`
and a fraction of the area's spine (`walNamesRes`, `Inv.lean`), and lends half of each: a fraction of
`osPathS R dir _ j`, kept by the borrower (never returned: the claim never changes again).

* `walInvBody_dirPath`: with the lock's record of no pending registration (`walNamesFrag none`: every
  present WAL registered) and the WAL's key, a fraction of the path to its directory.
* `walInv_dirPath`: the same at a program step (`notCrashed`); `openAtIndex` and `Open` take their
  paths from it (until 2026-11-14 the hypothesis `WalDirPathLaw`, the area's spine framed).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv
public import LinuxFs.Proof.os.MkdirAllParts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **A path to a registered WAL's directory**, lent by the invariant (see the file header). -/
theorem walInvBody_dirPath (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (j : Ino) (X : List GoString) :
    ⊢ walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s -∗ walNamesFrag (W := W) none -∗
      walDirKey (W := W) dir j X ==∗
      walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s ∗ walNamesFrag (W := W) none ∗
        ∃ q : Qp, osPathS (L := hG.goose_localGS) R dir (DFrac.own q) j := by
  iintro Hb Hf #Hk
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, HKa, Hca, %HDK⟩, %HAt, Hnms, Hbd⟩
  icases walDirKey_lookup (W := W) K dir j X $$ HKa Hk with %hK
  obtain ⟨lay, -, hl, rfl, -⟩ := HDK.1 dir j X hK
  unfold walNamesRes
  icases Hnms with ⟨%o, %Wn, Ha, Hs, %hf, ⟨%qs, Hsp⟩, Hl⟩
  icases walNames_agree (W := W) o none $$ Ha Hf with %ho
  subst ho
  have hm : lay.nm ∈ Wn := hf.2 dir lay hl (by simp)
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
  icases (BigSepL.bigSepL_lookup_acc hi).1 $$ Hl with ⟨Hn, Hl⟩
  unfold nameShare
  icases Hn with ⟨%q, %hn, Hn, %hq⟩
  obtain ⟨hnok, hwnm, hcur⟩ := hq
  -- the directory's path: `dir = r/nm`
  obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir = some d := by
    cases h' : s.wal !! dir with
    | none => rw [HW.2.1 dir h'] at hl; cases hl
    | some d => exact ⟨d, rfl⟩
  obtain ⟨l2, nm2, -, hl2, hin2, -, hnm2, -⟩ := HW.1 dir d hd
  rw [hl] at hl2; cases hl2
  have hdir : dir = child r lay.nm := by
    rw [hin2.2, Har, ← hnm2]; simp [child, List.append_assoc]; rfl
  -- half of each, and a common fraction of the halves lent
  obtain ⟨e, a, b, hea, heb⟩ := os.qp_common q.half qs.half
  have hsN : ∀ (x y z : Qp), x = y + z →
      osNames (L := hG.goose_localGS) jr (.only [lay.nm]) (DFrac.own x) hn ⊢
        osNames (L := hG.goose_localGS) jr (.only [lay.nm]) (DFrac.own y) hn ∗
        osNames (L := hG.goose_localGS) jr (.only [lay.nm]) (DFrac.own z) hn := fun x y z h => by
    subst h; exact (osNames_frac (L := hG.goose_localGS) jr (.only [lay.nm]) y z hn).1
  have hsP : ∀ (x y z : Qp), x = y + z →
      osPathS (L := hG.goose_localGS) R r (DFrac.own x) jr ⊢
        osPathS (L := hG.goose_localGS) R r (DFrac.own y) jr ∗
        osPathS (L := hG.goose_localGS) R r (DFrac.own z) jr := fun x y z h => by
    subst h; exact (osPathS_frac (L := hG.goose_localGS) R r y z jr).1
  icases hsN q q.half q.half (Qp.half_add_half q).symm $$ Hn with ⟨Hn, Hn2⟩
  icases hsN q.half e a hea.symm $$ Hn2 with ⟨Hne, -⟩
  icases hsP qs qs.half qs.half (Qp.half_add_half qs).symm $$ Hsp with ⟨Hsp, Hsp2⟩
  icases hsP qs.half e b heb.symm $$ Hsp2 with ⟨Hspe, -⟩
  ihave Hpath := osPathS_child (L := hG.goose_localGS) R r lay.nm (DFrac.own e) jr lay.j hn hnok
    (hcur dir lay hl rfl) $$ Hspe Hne
  have hset : Wn.set i lay.nm = Wn := by
    obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp hi
    rw [← he]; exact List.set_getElem_self hlt
  imodintro
  iframe Hf
  isplitr [Hpath]
  · iexists Ls, cl, n, F
    iframe
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
    isplitr
    · ipureintro; exact HDK
    isplitr
    · ipureintro; exact HAt
    isplitr
    · ipureintro; exact hf
    ispecialize Hl $$ %(lay.nm)
    rw [hset]
    iapply Hl
    iexists q.half, hn
    iframe Hn
    ipureintro; exact ⟨hnok, hwnm, hcur⟩
  · iexists e; rw [hdir]; iexact Hpath

/-- **A path to a registered WAL's directory, at a program step** (`notCrashed`), with the lock's
`walNamesFrag none` (which `walParked_lock`, the pin's, hands the taker). -/
theorem walInv_dirPath (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (j : Ino) (X : List GoString) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ walNamesFrag (W := W) none -∗
      walDirKey (W := W) dir j X ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ walNamesFrag (W := W) none ∗
        ∃ q : Qp, osPathS (L := hG.goose_localGS) R dir (DFrac.own q) j := by
  iintro #Hinv Hnc Hf #Hk
  imod walInv_open (L := hG.goose_localGS) C Mr R jr r ⊤ (fun _ _ => CoPset.mem_full) $$ Hinv Hnc
    with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  imod walInvBody_dirPath C Mr R jr r s dir j X $$ Hb Hf Hk with ⟨Hb, Hf, Hp⟩
  imod Hcl $$ [Hb] with -
  · iexists s; iexact Hb
  imodintro
  iframe

end iris

end WalFs
end EtcdGrove
end Perennial

end
