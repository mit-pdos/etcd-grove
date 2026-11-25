/- Lean-first (no Rocq counterpart).

# A purge's removal of a leftover file (unit `locks`, session 10; `notes/wal-units/locks.md`)

`purgeRound` (the tester's round of `fileutil.purgeFile`'s loop) removes the oldest names of the WAL
directory ending in `"wal"`, not only its `.wal` names (`walNameP`): a leftover file whose name ends in
`"wal"` but not in `".wal"` (none the WAL makes, but the invariant does not exclude one: the claim's others,
`walOthers`) may be removed too. Such a removal moves nothing of the WAL: the crash conditions and the
layouts read only `.wal` names (`nonwalHist_pure`, as `Repair`'s create of its `.broken` file), so it has
its own update, simpler than a segment's (`walPurge_osAUnc`): no client commit, the state unchanged, the
removed file's entry dropped from the claim's others (`walParked_rmOther`).

* `treeNearW_treeSetE`, `nonWalCrash_rm`: a crash of the claims after the removal is one of the claims
  before it on a tree agreeing but at the directory's non-`.wal` names.
* `rmOtherCommit_pure`: the invariant's pure conjuncts after the removal.
* `walParked_rmOther`: the parked resources (the claim out, its others fewer).
* `walPurgeOther_osAUnc`: the update for `os.Remove.specFileSncN`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeAu
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.BrokenPure

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- Setting a non-`.wal` entry of `j`: a tree agreeing but at `j`'s non-`.wal` names. -/
theorem treeNearW_treeSetE {j : Ino} {bt : GoString} (hbt : walNameP bt = false) (m : Tree)
    (v : Option Node) : TreeNearW j (treeSetE m j bt v) m := by
  intro j' b hb
  rw [treeSetE_entry]
  split
  · rename_i h
    obtain ⟨rfl, rfl⟩ := h
    rw [hb rfl] at hbt; cases hbt
  · rfl

/-- **A crash of the claims after a removal at a non-`.wal` name** (logged in the coherent claim
`(j, N, h)`, writing only `bt`, which no other claim of `j` holds). -/
theorem nonWalCrash_rm {cl : List Claim} {j : Ino} {N : NameSet} {h : NamesH} {x : Nat} {e : LogEntry}
    {c : Ents} {bt : GoString} (hcl : (j, N, h) ∈ cl) (hcoh : ClaimCoh h j N) (hs : h.next ≤ e.start)
    (hbt : ∀ b, N.Mem b → e.op.Writes j b → b = bt)
    (hothers : ∀ c' ∈ cl, c' ≠ (j, N, h) → c'.1 = j → ¬ c'.2.1.Mem bt) (hbtw : walNameP bt = false) :
    NonWalCrash cl (replClaim (j, N, h) (j, N, h.log x e c) cl) j := by
  intro n m' hr
  rcases regionCrashed_purge hr hcl hcoh hs hbt hothers with hr' | hr'
  · exact ⟨_, hr', treeNearW_treeSetE hbtw m' _⟩
  · exact ⟨m', hr', treeNearW_refl j m'⟩

/-- **The pure facts after the removal of a leftover file** (see the file header): the file `i` at the
non-`.wal` name `bt` of the keyed WAL directory's claim `(j, .except X, hj)`, `bt` not left out. -/
theorem rmOtherCommit_pure {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {CR : GMap GoString (NameSet × NamesH × Ino)} {K : GMap GoString (Ino × List GoString)}
    {cp : Option GoString} {dir : GoString} {lay : WalLay} {j : Ino} {X : List GoString} {hj : NamesH}
    {bt : GoString} {i : Ino} {x s0 : Nat}
    (hW : WalsOk C Mr R jr s Ls cl n) (hWC : WalsCreateOk jr cl) (hCO : CreatingOk jr cl CR)
    (hAN : AbsentNone s jr cl n) (hNm : WalsNamed Ls cl n)
    (hDK : DirKeysOk C Mr jr s Ls cl n K cp) (hAt : WalsAt jr Ls cl)
    (hK : K !! dir = some (j, X)) (hl : Ls !! dir = some lay)
    (hc0 : ClaimOnce (j, .except X, hj) cl)
    (hcur : hj.cur !! bt = some (.file i)) (hbtw : walNameP bt = false) (hbN : bt ∉ X)
    (hs0 : hj.next ≤ s0) (hsx : s0 ≤ x) :
    let cl' := replClaim (j, .except X, hj) (purgeClaim j X hj bt i x s0) cl
    WalsOk C Mr R jr s Ls cl' n ∧ WalsCreateOk jr cl' ∧ CreatingOk jr cl' CR ∧
      AbsentNone s jr cl' n ∧ WalsNamed Ls cl' n ∧ DirKeysOk C Mr jr s Ls cl' n K cp ∧
      WalsAt jr Ls cl' := by
  classical
  unfold purgeClaim
  obtain ⟨lay1, hj1, hl1, hlj, hjjr, hX, -, hcoh1, hexcl1⟩ := hDK.1 dir j X hK
  rw [hl] at hl1
  cases hl1
  subst hlj
  have hcl : (lay.j, NameSet.except X, hj) ∈ cl := claimOnce_mem hc0
  have hj1e := walClaim_eq hexcl1 hX hcl
  simp only [Prod.mk.injEq, true_and] at hj1e
  subst hj1e
  obtain ⟨X2, hj2, hD2, hx2⟩ := hDK.2.2 dir lay hl
  obtain ⟨hXe, hje2⟩ := hD2.eq_of_mem hX hcl
  rw [← hXe, ← hje2] at hx2
  have hst : hj.next ≤ (rmFileEnt lay.j bt i s0).start := hs0
  have hbt' : ∀ b, (NameSet.except X).Mem b → (rmFileEnt lay.j bt i s0).op.Writes lay.j b → b = bt :=
    fun b _ hw => ((rmFileEnt_writes _ _ _ _ _ _).1 hw).2
  have hothers : ∀ c' ∈ cl, c' ≠ (lay.j, NameSet.except X, hj) → c'.1 = lay.j →
      ¬ c'.2.1.Mem bt := fun c' hc hne hcj => hx2.2 c' hc hne hcj bt hbN
  have hcoh' : ClaimCoh (hj.log x (rmFileEnt lay.j bt i s0) (purgeNames X bt hj)) lay.j (.except X) := by
    refine claimCoh_log _ _ _ _ _ _ hcoh1 (Nat.le_trans hs0 hsx) (fun b hb hw => ?_)
    have hne : b ≠ bt := fun eb => hw ((rmFileEnt_writes _ _ _ _ _ _).2 ⟨rfl, eb⟩)
    exact purgeNames_lookup hb hne
  have hc : ∀ b, walNameP b = true → purgeNames X bt hj !! b = hj.cur !! b := by
    intro b hb
    refine purgeNames_lookup (fun hm => ?_) (fun e => ?_)
    · rw [hX b hm] at hb; cases hb
    · rw [e, hbtw] at hb; cases hb
  exact nonwalHist_pure hW hWC hCO hAN hNm hDK hAt hK hl hc0 hcoh' hc
    (fun b hb hw J => by rw [hbt' b hb hw, purgeNames_bt]; simp)
    (nonWalCrash_rm hcl hcoh1 hst hbt' hothers hbtw)
    (fun hdo => dirsOk_purge hdo hcl hcoh1 hst hbt' hcur hothers)
    (fun hjjr' han => absentNone_purge han hjjr' hcl hcoh1 hst hbt' hothers)

end pure

section parked
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The parked resources after the removal of a leftover file**: the WAL directory's claim `c` (out: its
key in the handle's record) replaced by `c'` with the same key and, off the `.wal` names, no more entries. -/
theorem walParked_rmOther (Ls : GMap GoString WalLay) (l1 l2 : List Claim) (c c' : Claim) (F : GMap Ino SegFl)
    (o : WalOut) (hkey : c'.1 = c.1 ∧ c'.2.1 = c.2.1) (hD : (c.1, c.2.1) ∈ o.D)
    (hsub : ∀ b n, walNameP b = false → c'.2.2.cur !! b = some n → c.2.2.cur !! b = some n) :
    ⊢ walParked (L := L) (W := W) Ls (l1 ++ c :: l2) F -∗ walOutFrag (W := W) o -∗
      walParked (L := L) (W := W) Ls (l1 ++ c' :: l2) F ∗ walOutFrag (W := W) o := by
  classical
  unfold walParked
  iintro ⟨%bf, %o', Ha, Hoa, %hb, Hs, Hc, Ht, Hw⟩ Hf
  icases walOut_agree (W := W) o' o $$ Hoa Hf with %ho
  subst ho
  iframe Hf
  iexists bf, o'
  iframe Ha Hoa Hs Ht
  isplitr
  · ipureintro; exact hb
  isplitl [Hc]
  · icases (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ Hc with ⟨H1, H2⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H2 with ⟨-, H2⟩
    iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
    iframe H1
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    iframe H2
    have e : ¬ ParkedClaim Ls o'.D c' := fun h => h.2 (by rw [hkey.1, hkey.2]; exact hD)
    rw [if_neg e]
    iempintro
  · iapply walOthersL_replSub (L := L) (fun c1 _ h => h)
      (fun h => ⟨(walDirClaimOf_key hkey.1 hkey.2).1 h, ?_⟩) $$ Hw
    intro b n hbn
    rw [othersOf_lookup] at hbn ⊢
    rw [hkey.1] at hbn
    split at hbn
    · next hc0 => rw [if_pos hc0]; exact hsub b n hc0.1 hbn
    · cases hbn

end parked

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **What a purge holds for a leftover's removal**: the directory's key, a quarter of the WAL claim (the
call has another), the handle's record of what is out. -/
def walPurgeOP (dir : GoString) (I : GMap GoString Nat) (j : Ino) (X : List GoString) (hj : NamesH) (o : WalOut) : IProp GF :=
  iprop(walDirKey (W := W) dir (incOf I dir) j X ∗ walIncQ (W := W) I ∗
    osNames j (.except X) (DFrac.own qQuarter) hj ∗ walOutFrag (W := W) o)

/-- **What a purge gets from a leftover's removal**: with no effect, what it held; after the commit
(logged at `x` by a call begun at `s0`), the claim's new history (a quarter). -/
def walPurgeOQ (dir : GoString) (I : GMap GoString Nat) (j : Ino) (X : List GoString) (hj : NamesH) (o : WalOut) (bt : GoString)
    (i : Ino) : Option (Nat × Nat) → IProp GF
  | none => walPurgeOP (W := W) dir I j X hj o
  | some (x, s0) => walPurgeOP (W := W) dir I j X (purgeClaim j X hj bt i x s0).2.2 o

/-- **A purge's update for `os.Remove.specFileSncN` of a leftover file** (see the file header): the file
`i` at `bt`, a non-`.wal` name of the claim (not left out). -/
theorem walPurgeOther_osAUnc (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (I : GMap GoString Nat) (j : Ino) (X : List GoString) (hj : NamesH) (o : WalOut) (bt : GoString)
    (i : Ino) (hoD : (j, NameSet.except X) ∈ o.D) (hcur : hj.cur !! bt = some (.file i))
    (hbtw : walNameP bt = false) (hbN : bt ∉ X) :
    ⊢ walInv (W := W) walCodec Mr R jr r -∗ walPurgeOP (W := W) dir I j X hj o -∗
      osAUnc (osNames j (.except X) (DFrac.own ((1 : Qp).half + qQuarter)) hj)
        (rmFileOutN j (.except X) bt i hj (DFrac.own ((1 : Qp).half + qQuarter)))
        (walPurgeOQ (W := W) dir I j X hj o bt i) := by
  iintro #Hinv HP
  iapply osAUnc_coiter _ _ _ (walPurgeOP (W := W) dir I j X hj o) $$ [] HP
  iintro !> HP
  unfold osAUncPre
  iintro Hnc
  imod walInv_open walCodec Mr R jr r osAuMask walN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  rw [show osAuMask \ (↑walN : CoPset) = walAuMask from rfl]
  icases Hb with ⟨%s, Hb⟩
  unfold walPurgeOP
  icases HP with ⟨#Hkey, HIq, Hq, Ho⟩
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl0, #Hcm, Hlays, %Hok, %Hco, ⟨%CR, Hcra, %Hcro⟩,
    Htl, %Han, %Hnm, Hpk, ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  icases walDirKey_lookupI K dir j X I $$ Hdk Hkey HIq with %HK
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
    dsimp only
    iframe Hkey HIq Hq Ho
  · iintro %oc Hβ
    rcases oc with _ | ⟨x, s0⟩
    · -- no effect: as the abort
      unfold rmFileOutN
      simp only [logOut, claimOut]
      icases Hβ with ⟨-, Hw⟩
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
      dsimp only [walPurgeOQ, walPurgeOP]
      iframe Hkey HIq Hq Ho
    · imod Hcl'
      unfold rmFileOutN
      simp only [logOut, claimOut]
      icases Hβ with ⟨⟨%hls, Hlog⟩, Hwn⟩
      unfold osLogged
      icases Hlog with ⟨%hsx, -, -⟩
      simp only [rmFileEnt] at hsx
      icases (osNames_frac j (.except X) (1 : Qp).half qQuarter _).1 $$ Hwn with ⟨Hαn, Hqn⟩
      obtain ⟨hok', hco', hcro', han', hnm', hdko', hat'⟩ := rmOtherCommit_pure (x := x) (s0 := s0)
        Hok Hco Hcro Han.1 Hnm Hdko HAt HK hl1 ⟨l1, l2, rfl, hn1, hn2⟩ hcur hbtw hbN hls hsx
      icases walParked_rmOther Ls l1 l2 (j, NameSet.except X, hj1) (purgeClaim j X hj1 bt i x s0) F o
        ⟨rfl, rfl⟩ hoD (fun b' n' _ h => purgeNames_sub h) $$ Hpk Ho with ⟨Hpk, Ho⟩
      imod Hcl $$ [Hg Hl1 Hαn Hl2 Hlays Hcra Htl Hpk Hdk Hcp Hnms]
      · iexists s
        iexists Ls, replClaim (j, NameSet.except X, hj1) (purgeClaim j X hj1 bt i x s0)
            (l1 ++ (j, NameSet.except X, hj1) :: l2), n, F
        iframe Hg Hcm Hlays Htl
        isplitr
        · ipureintro; exact Har
        isplitl [Hl1 Hαn Hl2]
        · rw [replClaim_split hn1 hn2]
          iapply (osClaims_split _ _ _ _).2
          iframe Hl1 Hl2
          dsimp only [purgeClaim, purgeNames]
          iexact Hαn
        isplitr
        · ipureintro; exact hok'
        isplitr
        · ipureintro; exact hco'
        isplitl [Hcra]
        · iexists CR
          iframe Hcra
          ipureintro; exact hcro'
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
        isplitr
        · ipureintro; exact hat'
        iframe Hnms; ipureintro; exact Hbd
      imodintro
      dsimp only [walPurgeOQ, walPurgeOP, purgeClaim, purgeNames]
      iframe Hkey HIq Hqn Ho
end iris

end WalFs
end EtcdGrove
end Perennial

end
