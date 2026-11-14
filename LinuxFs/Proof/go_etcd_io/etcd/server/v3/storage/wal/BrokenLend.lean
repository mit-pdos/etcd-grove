/- Lean-first (no Rocq counterpart).

# The WAL directory's others lent and given back (law L3's leftover `.broken`; `notes/wal-fsext-plan.md`,
W7-W12 log, eleventh session)

The invariant owns the files at a WAL directory claim's non-`.wal` names (`walOthersL`, in `walParked`),
but those lent: a name `bt` lent is recorded as the pseudo-key `lendKey j bt` in the record of what is
out (`WalOut.D`). `Repair` holds the claim out (its key in `o.D`, the directory's key `walDirKey dir j X`
and the claim's program half at the history `hj`), so it knows what the claim holds at `bt`:

* `walInv_lendOther`: a leftover file at `bt` (`hj.cur !! bt = some n`), lent: its `tmpEnt` (the file
  whole, `trFile`, what `os.OpenFile.wp_truncS` takes for the `O_TRUNC` open), the record with `lendKey j bt`;
* `walInv_unlendOther`: given back (after the create, `walBroken_osAUnc` lends the new file; after the
  `O_TRUNC` open, the file it truncated), the record without `lendKey j bt`.

Both over `walInvBody_dirClaim`: the invariant's `walParked` at the claims split at the key's claim, with
the facts the others need (the claim a WAL directory's, no other WAL directory claim of `j`:
`DirClaimOk`'s exclusivity on the `.wal` names), and the way back.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.BrokenAu

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- No other claim of a keyed WAL directory's is a WAL directory's claim of the same directory: it
would hold a `.wal` name (`DirClaimOk`'s exclusivity). -/
theorem dirClaim_noOther {Ls : GMap GoString WalLay} {l1 l2 : List Claim} {j : Ino}
    {X : List GoString} {hj : NamesH}
    (hn1 : (j, NameSet.except X, hj) ∉ l1) (hn2 : (j, NameSet.except X, hj) ∉ l2)
    (hexcl : ∀ c' ∈ l1 ++ (j, NameSet.except X, hj) :: l2, c' ≠ (j, NameSet.except X, hj) →
      c'.1 = j → ∀ b, walNameP b = true → ¬ c'.2.1.Mem b) :
    ∀ c1 ∈ l1 ++ l2, WalDirClaimOf Ls c1 → c1.1 ≠ j := by
  rintro c1 hc1 ⟨-, -, -, -, X1, hX1, hX1w⟩ hj1
  have hne : c1 ≠ (j, NameSet.except X, hj) := by
    rintro rfl
    rcases List.mem_append.1 hc1 with h | h
    · exact hn1 h
    · exact hn2 h
  refine hexcl c1 (List.mem_append.2 ((List.mem_append.1 hc1).imp id (List.mem_cons_of_mem _)))
    hne hj1 go!".wal" walNameP_dotWal ?_
  rw [hX1]
  show go!".wal" ∉ X1
  intro hm
  have h := hX1w _ hm
  rw [walNameP_dotWal] at h; cases h

/-- **The invariant's parked state at a keyed WAL directory's claim** (the claim's program half
agreeing with the invariant's): the claims split at it, the facts its others need, and the way back. -/
theorem walInvBody_dirClaim (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (dq : DFrac) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walDirKey (W := W) dir j X -∗
      osNames (L := L) j (.except X) dq hj -∗
      ∃ (Ls : GMap GoString WalLay) (l1 l2 : List Claim) (F : GMap Ino SegFl),
        ⌜WalDirClaimOf Ls (j, .except X, hj) ∧ ∀ c1 ∈ l1 ++ l2, WalDirClaimOf Ls c1 → c1.1 ≠ j⌝ ∗
        walParked (L := L) (W := W) Ls (l1 ++ (j, .except X, hj) :: l2) F ∗
        osNames (L := L) j (.except X) dq hj ∗
        (walParked (L := L) (W := W) Ls (l1 ++ (j, .except X, hj) :: l2) F -∗
          walInvBody (L := L) (W := W) C Mr R jr r s) := by
  iintro Hb #Hkey Hq
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
  iexists Ls, l1, l2, F
  iframe Hpk Hq
  isplitr
  · ipureintro
    exact ⟨⟨dir, lay1, hl1, hj1j.symm, X, rfl, hXw⟩, dirClaim_noOther hn1 hn2 hexcl⟩
  iintro Hpk
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

/-- **A WAL directory's leftover file lent** (`walParked`'s others; see the file header). -/
theorem walParked_lendOld (Ls : GMap GoString WalLay) (l1 l2 : List Claim) (c : Claim)
    (F : GMap Ino SegFl) (o : WalOut) (bt : GoString) (n : Node) (hW : WalDirClaimOf Ls c)
    (hoth : ∀ c1 ∈ l1 ++ l2, WalDirClaimOf Ls c1 → c1.1 ≠ c.1)
    (hw : walNameP bt = false) (hD : lendKey c.1 bt ∉ o.D) (hE : c.2.2.cur !! bt = some n) :
    ⊢ walParked (L := L) (W := W) Ls (l1 ++ c :: l2) F -∗ walOutFrag (W := W) o ==∗
      walParked (L := L) (W := W) Ls (l1 ++ c :: l2) F ∗
        walOutFrag (W := W) (o.addClaim (lendKey c.1 bt)) ∗ tmpEnt (hG := ⟨G, L⟩) (some n) := by
  unfold walParked
  iintro ⟨%bf, %o', Ha, Hoa, %hb, Hs, Hc, Ht, Hw⟩ Hf
  icases walOut_agree (W := W) o' o $$ Hoa Hf with %ho
  subst ho
  imod walOut_set (W := W) o' o' (o'.addClaim (lendKey c.1 bt)) $$ Hoa Hf with ⟨Hoa, Hf⟩
  unfold walOthersL
  icases (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ Hw with ⟨H1, H2⟩
  icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H2 with ⟨Hc0, H2⟩
  rw [if_pos hW]
  icases walOthers_lend (L := L) hw hD hE $$ Hc0 with ⟨Hn, Hc0⟩
  imodintro
  iframe Hf Hn
  iexists bf, o'.addClaim (lendKey c.1 bt)
  dsimp only [WalOut.addClaim]
  iframe Ha Hoa Hs Ht
  isplitr
  · ipureintro; exact hb
  have hPk : ∀ x : Claim, ParkedClaim Ls (lendKey c.1 bt :: o'.D) x ↔ ParkedClaim Ls o'.D x := by
    intro x
    unfold ParkedClaim
    constructor
    · rintro ⟨hx, hxD⟩; exact ⟨hx, fun hm => hxD (List.mem_cons_of_mem _ hm)⟩
    · rintro ⟨hx, hxD⟩
      refine ⟨hx, fun hm => hxD ?_⟩
      rcases List.mem_cons.1 hm with he | hm
      · obtain ⟨-, -, -, -, X, hX, -⟩ := hx
        simp only [lendKey, Prod.mk.injEq] at he
        rw [hX] at he; cases he.2
      · exact hm
  isplitl [Hc]
  · iapply BigSepL.bigSepL_mono (fun {k x} _ => ?_) $$ Hc
    simp only [propext (hPk x)]
    exact .rfl
  have hm := fun (l : List Claim) (hl : ∀ c1 ∈ l, WalDirClaimOf Ls c1 → c1.1 ≠ c.1) =>
    walOthersL_mono (L := L) (Ls := Ls) (Ls' := Ls) (D := o'.D) (D' := lendKey c.1 bt :: o'.D)
      (cl := l) (fun c1 hc1 h1 => ⟨h1, othersOf_lend_ne (hl c1 hc1 h1)⟩)
  unfold walOthersL at hm
  iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
  isplitl [H1]
  · iapply hm l1 (fun c1 hc1 => hoth c1 (List.mem_append_left _ hc1)) $$ H1
  iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
  rw [if_pos hW]
  iframe Hc0
  iapply hm l2 (fun c1 hc1 => hoth c1 (List.mem_append_right _ hc1)) $$ H2

/-- **A lent file given back** (`walParked`'s others; see the file header). -/
theorem walParked_unlend (Ls : GMap GoString WalLay) (l1 l2 : List Claim) (c : Claim)
    (F : GMap Ino SegFl) (o : WalOut) (bt : GoString) (n : Node) (hW : WalDirClaimOf Ls c)
    (hoth : ∀ c1 ∈ l1 ++ l2, WalDirClaimOf Ls c1 → c1.1 ≠ c.1)
    (hw : walNameP bt = false) (hD : lendKey c.1 bt ∈ o.D) (hE : c.2.2.cur !! bt = some n) :
    ⊢ walParked (L := L) (W := W) Ls (l1 ++ c :: l2) F -∗ walOutFrag (W := W) o -∗
      tmpEnt (hG := ⟨G, L⟩) (some n) ==∗
      walParked (L := L) (W := W) Ls (l1 ++ c :: l2) F ∗
        walOutFrag (W := W) (o.delClaim (lendKey c.1 bt)) := by
  unfold walParked
  iintro ⟨%bf, %o', Ha, Hoa, %hb, Hs, Hc, Ht, Hw⟩ Hf Hn
  icases walOut_agree (W := W) o' o $$ Hoa Hf with %ho
  subst ho
  imod walOut_set (W := W) o' o' (o'.delClaim (lendKey c.1 bt)) $$ Hoa Hf with ⟨Hoa, Hf⟩
  unfold walOthersL
  icases (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ Hw with ⟨H1, H2⟩
  icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H2 with ⟨Hc0, H2⟩
  rw [if_pos hW]
  ihave Hc0 := walOthers_unlend (L := L) hw hD hE $$ [Hc0 Hn]
  · iframe Hc0 Hn
  imodintro
  iframe Hf
  iexists bf, o'.delClaim (lendKey c.1 bt)
  dsimp only [WalOut.delClaim]
  iframe Ha Hoa Hs Ht
  isplitr
  · ipureintro; exact hb
  have hPk : ∀ x : Claim, ParkedClaim Ls (o'.D.filter (· ≠ lendKey c.1 bt)) x ↔ ParkedClaim Ls o'.D x := by
    intro x
    unfold ParkedClaim
    constructor
    · rintro ⟨hx, hxD⟩
      refine ⟨hx, fun hm => hxD ?_⟩
      refine List.mem_filter.2 ⟨hm, ?_⟩
      obtain ⟨-, -, -, -, X, hX, -⟩ := hx
      simp only [ne_eq, decide_eq_true_eq]
      intro he
      simp only [lendKey, Prod.mk.injEq] at he
      rw [hX] at he; cases he.2
    · rintro ⟨hx, hxD⟩; exact ⟨hx, fun hm => hxD (List.mem_filter.1 hm).1⟩
  isplitl [Hc]
  · iapply BigSepL.bigSepL_mono (fun {k x} _ => ?_) $$ Hc
    simp only [propext (hPk x)]
    exact .rfl
  have hf : ∀ j' b, j' ≠ c.1 → (lendKey j' b ∈ o'.D.filter (· ≠ lendKey c.1 bt) ↔ lendKey j' b ∈ o'.D) := by
    intro j' b hj'
    simp only [List.mem_filter, ne_eq, lendKey_inj, hj', false_and, not_false_eq_true, decide_true,
      and_true]
  have hm := fun (l : List Claim) (hl : ∀ c1 ∈ l, WalDirClaimOf Ls c1 → c1.1 ≠ c.1) =>
    walOthersL_mono (L := L) (Ls := Ls) (Ls' := Ls) (D := o'.D) (D' := o'.D.filter (· ≠ lendKey c.1 bt))
      (cl := l) (fun c1 hc1 h1 => ⟨h1, othersOf_congrD _ (hf c1.1 · (hl c1 hc1 h1))⟩)
  unfold walOthersL at hm
  iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
  isplitl [H1]
  · iapply hm l1 (fun c1 hc1 => hoth c1 (List.mem_append_left _ hc1)) $$ H1
  iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
  rw [if_pos hW]
  iframe Hc0
  iapply hm l2 (fun c1 hc1 => hoth c1 (List.mem_append_right _ hc1)) $$ H2

/-- **`Repair`'s leftover `.broken` lent** (see the file header), at any step: the claim out
(`hoD`), its program half at `hj` holding the file `n` at `bt`, a non-`.wal` name not yet lent. -/
theorem walInv_lendOther (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (E : CoPset) (hE : ↑walN ⊆ E) (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH)
    (dq : DFrac) (o : WalOut) (bt : GoString) (n : Node)
    (hw : walNameP bt = false) (hD : lendKey j bt ∉ o.D) (hcur : hj.cur !! bt = some n) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walDirKey (W := W) dir j X -∗ osNames (L := L) j (.except X) dq hj -∗ walOutFrag (W := W) o ={E}=∗
      notCrashed (hC := L.goose_crashGS) ∗ osNames (L := L) j (.except X) dq hj ∗
        walOutFrag (W := W) (o.addClaim (lendKey j bt)) ∗ tmpEnt (hG := ⟨G, L⟩) (some n) := by
  iintro #Hinv Hnc #Hk Hq Ho
  imod walInv_open C Mr R jr r E hE $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases walInvBody_dirClaim C Mr R jr r s dir j X hj dq $$ Hb Hk Hq with
    ⟨%Ls, %l1, %l2, %F, ⟨%hW, %hoth⟩, Hpk, Hq, Hback⟩
  imod walParked_lendOld Ls l1 l2 (j, .except X, hj) F o bt n hW hoth hw hD hcur $$ Hpk Ho
    with ⟨Hpk, Ho, Hn⟩
  imod Hcl $$ [Hback Hpk] with -
  · iexists s; iapply Hback $$ Hpk
  imodintro
  iframe Hnc Hq Ho Hn

/-- **A lent file of a WAL directory given back** (see the file header), at any step. -/
theorem walInv_unlendOther (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (E : CoPset) (hE : ↑walN ⊆ E) (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH)
    (dq : DFrac) (o : WalOut) (bt : GoString) (n : Node)
    (hw : walNameP bt = false) (hD : lendKey j bt ∈ o.D) (hcur : hj.cur !! bt = some n) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walDirKey (W := W) dir j X -∗ osNames (L := L) j (.except X) dq hj -∗ walOutFrag (W := W) o -∗
      tmpEnt (hG := ⟨G, L⟩) (some n) ={E}=∗
      notCrashed (hC := L.goose_crashGS) ∗ osNames (L := L) j (.except X) dq hj ∗
        walOutFrag (W := W) (o.delClaim (lendKey j bt)) := by
  iintro #Hinv Hnc #Hk Hq Ho Hn
  imod walInv_open C Mr R jr r E hE $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases walInvBody_dirClaim C Mr R jr r s dir j X hj dq $$ Hb Hk Hq with
    ⟨%Ls, %l1, %l2, %F, ⟨%hW, %hoth⟩, Hpk, Hq, Hback⟩
  imod walParked_unlend Ls l1 l2 (j, .except X, hj) F o bt n hW hoth hw hD hcur $$ Hpk Ho Hn
    with ⟨Hpk, Ho⟩
  imod Hcl $$ [Hback Hpk] with -
  · iexists s; iapply Hback $$ Hpk
  imodintro
  iframe Hnc Hq Ho

end iris

end WalFs
end EtcdGrove
end Perennial

end
