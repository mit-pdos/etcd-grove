/- Lean-first (no Rocq counterpart).

# `Repair`'s update at the `.broken` file's create (law L3; `notes/wal-fsext-plan.md`, W7-W12 log,
ninth and tenth sessions)

`walBroken_osAUnc`: the atomic update `Repair` gives `os.OpenFile.specCreateTruncSncN` for
`createNewWALFile(<seg>.wal.broken, true)` in the absent-name case: the name `bt` (a `.wal.broken`
name) is created in the WAL directory's claim `(j, .except X, hj)`, whose halves are the program's
(out, `(j, .except X) ∈ o.D`, with the key `walDirKey dir j X`) and the invariant's. As `walCut_osAUnc`
(`CutAu.lean`): the program keeps a quarter of its half in the update (`walBrokenP`), to agree with
the invariant's at the opening; the call gets the other quarter.

* *Opening*: opens `walInv`, finds the key's claim (`DirKeysOk`: once among the invariant's), agrees
  with the program's, hands out the invariant's half with the quarter.
* *Abort*, or a commit with no effect: closed again; the program's resources back.
* *Commit* (the create logged at `x` by a call begun at `s0`, the file `i`): the claim's history
  logged at `bt` (`replClaim`), every pure conjunct kept (`brokenCommit_pure`, over `brokenHist_pure`:
  `bt` is in the claim and in no other claim of `j`, `DirClaimExcl`), `walParked` unchanged (the
  claim is out, its element `emp` either way: `walParked_replOut`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.BrokenPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutAu
public import LinuxFs.Spec.os.OpenFileTruncSN

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- A `.wal.broken` name is not a `.wal` name. -/
theorem walNameP_broken {b : GoString} (hb : go!".wal.broken" <:+ b) : walNameP b = false := by
  unfold walNameP
  apply decide_eq_false
  intro hw
  have h : go!".wal" <:+ go!".wal.broken" :=
    List.suffix_of_suffix_length_le hw hb (by decide)
  exact absurd h (by decide)

/-- A file's create writes only its own slot. -/
private theorem crEnt_writes {j j' : Ino} {b b' : GoString} {i : Ino} {s : Nat}
    (h : (crEnt j b i s).op.Writes j' b') : j' = j ∧ b' = b := by
  rcases h with h | ⟨j0, b0, h⟩
  · simp only [crEnt, MetaOp.slots, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at h
    exact h
  · cases h

/-- **The pure facts after the create of the `.wal.broken` name `bt` in a keyed WAL directory's
claim** (`brokenHist_pure` with the create's entry): the key gives the claim (once, exclusive on all
its names: `DirClaimsOk`), so `bt` is in it and in no other claim of `j`. -/
theorem brokenCommit_pure {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {CR : GMap GoString (NameSet × NamesH × Ino)} {K : GMap GoString (Ino × List GoString)}
    {cp : Option GoString} {dir : GoString} {j : Ino} {X : List GoString} {hj : NamesH}
    {x s0 : Nat} {i : Ino} {bt : GoString}
    (hW : WalsOk C Mr R jr s Ls cl n) (hWC : WalsCreateOk jr cl) (hCO : CreatingOk jr cl CR)
    (hAN : AbsentNone s jr cl n) (hNm : WalsNamed Ls cl n)
    (hDK : DirKeysOk C Mr jr s Ls cl n K cp) (hAt : WalsAt jr Ls cl)
    (hK : K !! dir = some (j, X)) (hcl : (j, NameSet.except X, hj) ∈ cl)
    (hbt : go!".wal.broken" <:+ bt) (hcur : hj.cur !! bt = none) (hs : hj.next ≤ s0)
    (hsx : s0 ≤ x) :
    let cl' := replClaim (j, .except X, hj)
      (j, .except X, hj.log x (crEnt j bt i s0) (<[bt := .file i]> hj.cur)) cl
    WalsOk C Mr R jr s Ls cl' n ∧ WalsCreateOk jr cl' ∧ CreatingOk jr cl' CR ∧
      AbsentNone s jr cl' n ∧ WalsNamed Ls cl' n ∧ DirKeysOk C Mr jr s Ls cl' n K cp ∧
      WalsAt jr Ls cl' := by
  classical
  obtain ⟨lay, hj1, hl, hlj, hjjr, hX, honce, hcoh, hexcl⟩ := hDK.1 dir j X hK
  subst hlj
  have hD1 : DirClaimOk jr cl lay.j X hj1 := ⟨hjjr, hX, honce, hcoh, hexcl⟩
  obtain ⟨-, hje⟩ := hD1.eq_of_mem hX hcl
  subst hje
  obtain ⟨X2, hj2, hD2, hx2⟩ := hDK.2.2 dir lay hl
  obtain ⟨hXe, hje2⟩ := hD2.eq_of_mem hX hcl
  rw [← hXe, ← hje2] at hx2
  have hbX : bt ∉ X := fun hm => hx2.1 bt hm hbt
  have hbtw := walNameP_broken hbt
  have hcoh' : ClaimCoh (hj.log x (crEnt lay.j bt i s0) (<[bt := .file i]> hj.cur)) lay.j
      (.except X) :=
    claimCoh_log hj lay.j _ x _ _ hcoh (Nat.le_trans hs hsx) (fun b _ hnw => by
      rw [GMap.lookup_insert_ne]
      rintro rfl
      exact hnw (Or.inl (by simp [crEnt, MetaOp.slots])))
  exact brokenHist_pure hW hWC hCO hAN hNm hDK hAt hK hl honce hcoh'
    (fun b hb => by
      rw [GMap.lookup_insert_ne]
      rintro rfl
      rw [hbtw] at hb; cases hb)
    hs (fun b _ hw => (crEnt_writes hw).2) hcur
    (fun c' hc' hne hcj => hx2.2 c' hc' hne hcj bt hbX) hbtw

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **A claim out of `walParked` replaced by one of the same directory and names** (its element
`emp` before and after). -/
theorem walParked_replOut (Ls : GMap GoString WalLay) (l1 l2 : List Claim) (c c' : Claim)
    (F : GMap Ino SegFl) (o : WalOut) (hkey : c'.1 = c.1 ∧ c'.2.1 = c.2.1)
    (hD : (c.1, c.2.1) ∈ o.D) :
    ⊢ walParked (L := L) (W := W) Ls (l1 ++ c :: l2) F -∗ walOutFrag (W := W) o -∗
      walParked (L := L) (W := W) Ls (l1 ++ c' :: l2) F ∗ walOutFrag (W := W) o := by
  unfold walParked
  iintro ⟨%bf, %o', Ha, Hoa, %hb, Hs, Hc, Ht⟩ Hf
  icases walOut_agree (W := W) o' o $$ Hoa Hf with %ho
  subst ho
  iframe Hf
  iexists bf, o'
  iframe Ha Hoa Hs Ht
  isplitr
  · ipureintro; exact hb
  icases (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ Hc with ⟨H1, H2⟩
  icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H2 with ⟨-, H2⟩
  iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
  iframe H1
  iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
  iframe H2
  have e : ¬ ParkedClaim Ls o'.D c' := fun h => h.2 (by rw [hkey.1, hkey.2]; exact hD)
  rw [if_neg e]
  iempintro

end iris

section au
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **What `Repair` holds for the `.broken` create's update**: the directory's key, a quarter of
the WAL directory's claim (the call has another), the handle's record of what is out (the claim
among it). -/
def walBrokenP (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (o : WalOut) :
    IProp GF :=
  iprop(walDirKey (W := W) dir j X ∗ osNames j (.except X) (DFrac.own qQuarter) hj ∗
    walOutFrag (W := W) o)

/-- **What `Repair` gets from the update**: with no effect, what it held; after the create of `bt`
(the file `i`, logged at `x` by a call begun at `s0`), its quarter of the claim at the new history. -/
def walBrokenQ (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (o : WalOut)
    (bt : GoString) : Option (Nat × Nat × Ino) → IProp GF
  | none => walBrokenP (W := W) dir j X hj o
  | some (x, s0, i) => iprop(walDirKey (W := W) dir j X ∗
      osNames j (.except X) (DFrac.own qQuarter) (hj.log x (crEnt j bt i s0) (<[bt := .file i]> hj.cur)) ∗
      walOutFrag (W := W) o)

/-- **`Repair`'s update for `os.OpenFile.specCreateTruncSncN`** (see the file header): the name `bt`
a `.wal.broken` name, the claim out (`hoD`). -/
theorem walBroken_osAUnc (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (o : WalOut) (bt : GoString)
    (hoD : (j, NameSet.except X) ∈ o.D) (hbt : go!".wal.broken" <:+ bt) :
    ⊢ walInv (W := W) C Mr R jr r -∗ walBrokenP (W := W) dir j X hj o -∗
      osAUnc (osNames j (.except X) (DFrac.own ((1 : Qp).half + qQuarter)) hj)
        (crOutN j (.except X) bt hj (DFrac.own ((1 : Qp).half + qQuarter)))
        (walBrokenQ (W := W) dir j X hj o bt) := by
  iintro #Hinv HP
  iapply osAUnc_coiter _ _ _ (walBrokenP (W := W) dir j X hj o) $$ [] HP
  iintro !> HP
  unfold osAUncPre
  iintro Hnc
  imod walInv_open C Mr R jr r osAuMask walN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  rw [show osAuMask \ (↑walN : CoPset) = walAuMask from rfl]
  icases Hb with ⟨%s, Hb⟩
  unfold walBrokenP
  icases HP with ⟨#Hkey, Hq, Ho⟩
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl0, #Hcm, Hlays, %Hok, %Hco, ⟨%CR, Hcra, %Hcro⟩,
    Htl, %Han, %Hnm, Hpk, ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  icases walDirKey_lookup K dir j X $$ Hdk Hkey with %HK
  obtain ⟨lay1, hj1, hl1, hj1j, hjjr, hXw, honce, hcoh, hexcl⟩ := Hdko.1 dir j X HK
  obtain ⟨l1, l2, hcl, hn1, hn2⟩ := honce
  subst hcl
  icases (osClaims_split _ _ _ _).1 $$ Hcl0 with ⟨Hl1, Hα, Hl2⟩
  icases osNames_agree j (.except X) _ _ hj1 hj $$ Hα Hq with %Hhj
  subst Hhj
  ihave Hw := (osNames_frac j (.except X) (1 : Qp).half qQuarter hj1).2 $$ [Hα Hq]
  · iframe Hα Hq
  imod (fupd_mask_subseteq (show (∅ : CoPset) ⊆ walAuMask from
    Std.LawfulSet.empty_subset)) with Hcl'
  imodintro
  iframe Hw Hnc
  isplit
  · -- abort
    iintro Hw
    icases (osNames_frac j (.except X) (1 : Qp).half qQuarter hj1).1 $$ Hw with ⟨Hα, Hq⟩
    imod Hcl'
    imod Hcl $$ [Hg Hl1 Hα Hl2 Hlays Hcra Htl Hpk Hdk Hcp Hnms]
    · iexists s
      iexists Ls, l1 ++ (j, NameSet.except X, hj1) :: l2, n, F
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
        ipureintro; exact Hcro
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
    dsimp only [walBrokenP]
    iframe Hkey Hq Ho
  · iintro %oc Hβ
    rcases oc with _ | ⟨x, s0, i⟩
    · -- no effect: as the abort
      simp only [crOutN]
      icases (osNames_frac j (.except X) (1 : Qp).half qQuarter hj1).1 $$ Hβ with ⟨Hα, Hq⟩
      imod Hcl'
      imod Hcl $$ [Hg Hl1 Hα Hl2 Hlays Hcra Htl Hpk Hdk Hcp Hnms]
      · iexists s
        iexists Ls, l1 ++ (j, NameSet.except X, hj1) :: l2, n, F
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
          ipureintro; exact Hcro
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
      dsimp only [walBrokenQ, walBrokenP]
      iframe Hkey Hq Ho
    · imod Hcl'
      simp only [crOutN]
      icases Hβ with ⟨%hcs, Hlog, Hwn⟩
      unfold osLogged
      icases Hlog with ⟨%hsx, -, -⟩
      simp only [crEnt] at hsx
      icases (osNames_frac j (.except X) (1 : Qp).half qQuarter _).1 $$ Hwn with ⟨Hαn, Hqn⟩
      have hcl : (j, NameSet.except X, hj1) ∈ l1 ++ (j, NameSet.except X, hj1) :: l2 := by simp
      obtain ⟨hok', hwc', hco', han', hnm', hdko', hat'⟩ := brokenCommit_pure (i := i)
        Hok Hco Hcro Han.1 Hnm Hdko HAt HK hcl hbt hcs.1 hcs.2 hsx
      ihave Hpk := walParked_replOut Ls l1 l2 (j, NameSet.except X, hj1)
        (j, NameSet.except X, hj1.log x (crEnt j bt i s0) (<[bt := .file i]> hj1.cur)) F o
        ⟨rfl, rfl⟩ hoD $$ Hpk Ho
      icases Hpk with ⟨Hpk, Ho⟩
      imod Hcl $$ [Hg Hl1 Hαn Hl2 Hlays Hcra Htl Hpk Hdk Hcp Hnms]
      · iexists s
        iexists Ls, replClaim (j, NameSet.except X, hj1)
            (j, NameSet.except X, hj1.log x (crEnt j bt i s0) (<[bt := .file i]> hj1.cur))
            (l1 ++ (j, NameSet.except X, hj1) :: l2), n, F
        iframe Hg Hcm Hlays Htl
        isplitr
        · ipureintro; exact Har
        isplitl [Hl1 Hαn Hl2]
        · rw [replClaim_split hn1 hn2]
          iapply (osClaims_split _ _ _ _).2
          iframe Hl1 Hl2 Hαn
        isplitr
        · ipureintro; exact hok'
        isplitr
        · ipureintro; exact hwc'
        isplitl [Hcra]
        · iexists CR
          iframe Hcra
          ipureintro; exact hco'
        isplitr
        · ipureintro; exact ⟨han', Han.2⟩
        isplitr
        · ipureintro; exact hnm'
        isplitl [Hpk]
        · rw [replClaim_split hn1 hn2]; iexact Hpk
        isplitl [Hdk Hcp]
        · iexists K, cp
          iframe Hdk Hcp
          ipureintro; exact hdko'
        iframe Hnms; ipureintro; exact ⟨hat', Hbd⟩
      imodintro
      dsimp only [walBrokenQ]
      iframe Hkey Hqn Ho

end au

end WalFs
end EtcdGrove
end Perennial

end
