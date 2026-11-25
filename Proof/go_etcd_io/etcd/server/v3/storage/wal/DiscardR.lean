/- Lean-first (no Rocq counterpart).

# `Discard`'s rename, step R (P6b state C, mit-pdos/etcd-grove#50; `notes/wal-p6-handoff.md`, sessions 15-17)

`wal.Discard` renames the WAL's directory `r/nm` (inode `J`) onto `r/nm.tmp` in the claim
`(jr, .only [nm, tmp], h)` that U' (`DiscardSteps.lean`) made and the cleanup's pin
(`walInv_pinClean`, `CleanupAu.lean`) recorded. `discAU` is the update `os.Rename.specDirSnc` takes: as
`cleanAU` (the claim found by the pin, the claims logged by `movClaims`), but the real state changes: the
WAL at `dir` becomes **unnamed** (`unnameS`: a crash between the rename and the parent's fsync may keep or
lose its directory) and its incarnation is bumped (`walLeI_unname`; all five shares of the incarnations,
`walGhostI_bump`), and the client's first update `AU₁` commits at the same step.

* the pure part: the invariant's facts with `dir`'s WAL unnamed (`walsOk_unname`, `dirKeysOk_unname`,
  `absentNone_unname`), then `CleanupMoved.lean`'s `*_moved` over the unnamed state;
* the keys' authority loses `dir`'s key (`walDirKeysAuth_bump`: no key is recorded above the current
  incarnation), the pipeline reserve's eighth comes out of `walParked` (`walParked_incE`: the lock free, no
  pipeline name out).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DiscardSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CleanupAu
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateNamed

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- The rename's step: the WAL in `dir` unnamed. -/
def unnameS (s : AbsDiskState) (dir : GoString) : AbsDiskState :=
  absDiskUpd s dir (fun d => { d with named := false })

theorem unnameS_none {s : AbsDiskState} {dir : GoString} (hd : s.wal !! dir = none) :
    unnameS s dir = s := by
  unfold unnameS absDiskUpd; rw [hd]

theorem unnameS_wal {s : AbsDiskState} {dir : GoString} {d : WalDur} (hd : s.wal !! dir = some d) :
    (unnameS s dir).wal = <[dir := { d with named := false }]> s.wal :=
  absDiskUpd_wal s dir _ d hd

theorem unnameS_area (s : AbsDiskState) (dir : GoString) : (unnameS s dir).area = s.area :=
  absDiskUpd_area s dir _

theorem unnameS_dirs (s : AbsDiskState) (dir : GoString) : (unnameS s dir).dirs = s.dirs := by
  unfold unnameS absDiskUpd; split <;> rfl

theorem crashTo_unname {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {m' : Tree}
    {fo : Ino → Option Fs.OsFile} (h : CrashTo C Mr d lay m' fo) :
    CrashTo C Mr { d with named := false } lay m' fo := by
  rcases h with ⟨-, hn⟩ | hr
  · exact Or.inl ⟨rfl, hn⟩
  · exact Or.inr hr

theorem crashOkA_unname {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {alt : Option WalLay} {cl : List Claim} {n : Nat} (h : CrashOkA C Mr d lay alt cl n) :
    CrashOkA C Mr { d with named := false } lay alt cl n := fun m' fo hr hf hnm hw1 =>
  (h m' fo hr hf hnm hw1).imp crashTo_unname (fun ⟨l0, h0, hc⟩ => ⟨l0, h0, crashTo_unname hc⟩)

theorem crashOkW_unname {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {n : Nat} (h : CrashOkW C Mr d lay cl n) :
    CrashOkW C Mr { d with named := false } lay cl n := by
  obtain ⟨alt, halt, h⟩ := h
  refine ⟨alt, fun lay0 h0 => ?_, crashOkA_unname h⟩
  obtain ⟨⟨ents0, ha⟩, h1, h2, h3, h4⟩ := halt lay0 h0
  exact ⟨⟨ents0, walAbsD_named false ha⟩, h1, h2, h3, h4⟩

theorem walFullOk_unname {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {n : Nat} (h : WalFullOk C Mr d lay cl n) :
    WalFullOk C Mr { d with named := false } lay cl n :=
  ⟨let ⟨e, ha⟩ := h.1; ⟨e, walAbsD_named false ha⟩, crashOkW_unname h.2.1, h.2.2⟩

/-- **`WalsOk` with the WAL in `dir` unnamed** (its crash condition only weaker). -/
theorem walsOk_unname {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} (hok : WalsOk C Mr R jr s Ls cl n)
    (dir : GoString) : WalsOk C Mr R jr (unnameS s dir) Ls cl n := by
  cases hd : s.wal !! dir with
  | none => rw [unnameS_none hd]; exact hok
  | some d =>
    have hw := unnameS_wal (dir := dir) hd
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hok
    refine ⟨fun dir' d' hd' => ?_, fun dir' hn' => h2 dir' ?_, h3, h4, ?_, ?_⟩
    · rw [hw] at hd'
      by_cases he : dir' = dir
      · subst he
        rw [GMap.lookup_insert_eq] at hd'
        cases hd'
        obtain ⟨lay, nm', hj, hlay, hin', hjr, hnm, hcl, ha, hco⟩ := h1 dir' d hd
        exact ⟨lay, nm', hj, hlay, by rw [unnameS_area]; exact hin', hjr, hnm, hcl,
          walAbsD_named false ha, walFullOk_unname hco⟩
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hd'
        obtain ⟨lay, nm', hj, hlay, hin', rest⟩ := h1 dir' d' hd'
        exact ⟨lay, nm', hj, hlay, by rw [unnameS_area]; exact hin', rest⟩
    · rw [hw] at hn'
      by_cases he : dir' = dir
      · subst he; rw [GMap.lookup_insert_eq] at hn'; cases hn'
      · rwa [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hn'
    · intro dir' nm' hin' hn' m' hr J' hJ'
      rw [unnameS_area] at hin'
      rw [hw] at hn'
      by_cases he : dir' = dir
      · subst he; rw [GMap.lookup_insert_eq] at hn'; cases hn'
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hn'
        exact h5 dir' nm' hin' hn' m' hr J' hJ'
    · intro dd hdd m' hr
      rw [unnameS_dirs] at hdd
      exact h6 dd hdd m' hr

/-- **`DirKeysOk` with the WAL in `dir` unnamed**, over fewer keys. -/
theorem dirKeysOk_unname {C : WalCodec} {Mr : WalMarshal} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K K' : GMap GoString (Ino × List GoString)} {c : Option GoString}
    (hk : DirKeysOk C Mr jr s Ls cl n K c) (dir : GoString)
    (hK : ∀ d x, K' !! d = some x → K !! d = some x) :
    DirKeysOk C Mr jr (unnameS s dir) Ls cl n K' c := by
  refine ⟨fun d j X h => hk.1 d j X (hK _ _ h), fun dir' d' lay hd' hl hcd => ?_, hk.2.2⟩
  cases hd : s.wal !! dir with
  | none => rw [unnameS_none hd] at hd'; exact hk.2.1 dir' d' lay hd' hl hcd
  | some d =>
    rw [unnameS_wal hd] at hd'
    by_cases he : dir' = dir
    · subst he
      rw [GMap.lookup_insert_eq] at hd'; cases hd'
      exact crashOkA_unname (d := walFullD d lay.pg lay) (hk.2.1 dir' d lay hd hl hcd)
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hd'
      exact hk.2.1 dir' d' lay hd' hl hcd

/-- A WAL directory's name in the area is its path's. -/
theorem inArea_nm_inj {r dir nm nm' : GoString} (h : InArea r dir nm) (h' : InArea r dir nm') :
    nm' = nm := by
  have e := h'.2.symm.trans h.2
  exact List.append_cancel_left e

/-- **`DirKeysOk` with a key added** for a WAL's directory (its layout's directory, the pipeline names
excepted): `DirClaimsOk` gives the claim's facts the key records. (R records the discarded WAL's key at
its new incarnation, so that S finds the layout's directory: `walInv_discardS`.) -/
theorem dirKeysOk_addKey {C : WalCodec} {Mr : WalMarshal} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K : GMap GoString (Ino × List GoString)} {c : Option GoString}
    (hk : DirKeysOk C Mr jr s Ls cl n K c) {dir : GoString} {lay : WalLay} (hl : Ls !! dir = some lay) :
    DirKeysOk C Mr jr s Ls cl n (<[dir := (lay.j, walTmps)]> K) c := by
  refine ⟨fun d j X h => ?_, hk.2.1, hk.2.2⟩
  by_cases e : d = dir
  · subst e
    rw [GMap.lookup_insert_eq] at h
    cases h
    obtain ⟨X, hj, hok, hex⟩ := hk.2.2 d lay hl
    obtain ⟨hJr, hXn, honce, hcoh, hexc⟩ := hok
    have hX := hex.1
    subst hX
    exact ⟨lay, hj, hl, rfl, hJr, hXn, honce, hcoh, hexc⟩
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h
    exact hk.1 d j X h

/-- **Strong absence with the WAL in `dir` unnamed** (its WAL-less names unchanged). -/
theorem absentNone_unname {s : AbsDiskState} {jr : Ino} {cl : List Claim} {n : Nat}
    (h : AbsentNone s jr cl n) (dir : GoString) : AbsentNone (unnameS s dir) jr cl n := by
  intro dir' nm hin hnone
  rw [unnameS_area] at hin
  refine h dir' nm hin ?_
  cases hd : s.wal !! dir with
  | none => rw [unnameS_none hd] at hnone; exact hnone
  | some d =>
    rw [unnameS_wal hd] at hnone
    by_cases he : dir' = dir
    · subst he; rw [GMap.lookup_insert_eq] at hnone; cases hnone
    · rwa [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hnone

theorem walDurLe_unname {d ds : WalDur} (h : walDurLe d ds) :
    walDurLe { d with named := false } { ds with named := false } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, fun e => e⟩

/-- The incarnations after a bump of `dir`'s. -/
theorem incOf_bump (I : GMap GoString Nat) (dir k : GoString) :
    incOf (<[dir := incOf I dir + 1]> I) k = if k = dir then incOf I dir + 1 else incOf I k := by
  unfold incOf
  by_cases e : k = dir
  · subst e; rw [GMap.lookup_insert_eq]; simp
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; simp [e]

/-- **The keys after a bump of `dir`'s incarnation**: `dir`'s gone (`walDirKeysAuth_bump`'s premise). -/
theorem keys_bump (I : GMap GoString Nat) (K : GMap GoString (Ino × List GoString)) (dir : GoString) :
    (∀ d, incOf I d ≤ incOf (<[dir := incOf I dir + 1]> I) d) ∧
      ∀ d x, (GMap.delete dir K) !! d = some x ↔
        (incOf (<[dir := incOf I dir + 1]> I) d = incOf I d ∧ K !! d = some x) := by
  refine ⟨fun d => ?_, fun d x => ?_⟩
  · rw [incOf_bump]
    split
    · rename_i e; subst e; omega
    · omega
  · rw [incOf_bump]
    by_cases e : d = dir
    · subst e; simp
    · simp only [e, ite_false, true_and]; rw [GMap.lookup_delete_ne _ (Ne.symm e)]

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The free lock token less its quarter of the incarnations and its record of what is out**, to be
given back at any incarnations. -/
theorem walUnlockedTokX_open :
    walUnlockedTokX (W := W) ⊢ ∃ I : GMap GoString Nat, walIncQ (W := W) I ∗
      walOutFrag (W := W) WalOut.empty ∗
      ∀ I' : GMap GoString Nat, walIncQ (W := W) I' -∗ walOutFrag (W := W) WalOut.empty -∗
        walUnlockedTokX (W := W) := by
  unfold walUnlockedTokX walIncAny
  iintro ⟨H1, H2, H3, H4, H5, %I, H6⟩
  iexists I
  iframe H6 H4
  iintro %I' H6' H4'
  iframe H1 H2 H3 H4' H5
  iexists I'; iexact H6'

/-- **The pipeline reserve out of the parked state** (the lock free: the record of what is out empty,
`walOutFrag WalOut.empty`), to be given back at any value. -/
theorem walParked_incE (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl) :
    ⊢ walParked (L := L) (W := W) Ls cl F -∗ walOutFrag (W := W) WalOut.empty -∗
      ∃ I : GMap GoString Nat, walIncE (W := W) I ∗ walOutFrag (W := W) WalOut.empty ∗
        ∀ I' : GMap GoString Nat, walIncE (W := W) I' -∗ walParked (L := L) (W := W) Ls cl F := by
  have hT : WalOut.empty.T = [] := rfl
  iintro Hpk Ho
  unfold walParked
  icases Hpk with ⟨%b, %o, Hpa, Hoa, Hrest⟩
  icases walOut_agree o _ $$ Hoa Ho with %e
  subst e
  unfold walOutAuth
  icases Hoa with ⟨Hoa, HE⟩
  simp only [hT, ↓reduceIte]
  unfold walIncEAny
  icases HE with ⟨%I, HE⟩
  iexists I
  iframe HE Ho
  iintro %I' HE'
  iexists b, WalOut.empty
  iframe Hpa
  isplitl [Hoa HE']
  · iframe Hoa
    simp only [hT, ↓reduceIte]
    iexists I'; iexact HE'
  simp only [hT]
  iexact Hrest

end iris

section au
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- The client's first update (`wal.Discard.spec`'s `AU₁`). -/
abbrev discAU₁ (dir : GoString) (ic : Nat) (Q₁ : WalDur → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ d : WalDur, walDiskAtI (W := W) dir ic d }> @ walAuMask, ∅
    <{ walDiskAtI (W := W) dir (ic + 1) { d with named := false }, COMM Q₁ d }>)

/-- What the rename's update holds: the pin and the client's first update. -/
def discP (dir : GoString) (N : NameSet) (h : NamesH) (jr : Ino) (ic : Nat) (Q₁ : WalDur → IProp GF) :
    IProp GF :=
  iprop(walCleanPin (W := W) N h jr ∗ discAU₁ (W := W) dir ic Q₁)

/-- What the rename's update gives: with no effect, what it held; logged, the token, `AU₁`'s result and the
WAL's directory key at its new incarnation (`J`, the directory renamed: S finds the layout by it). -/
def discQ (dir : GoString) (N : NameSet) (h : NamesH) (jr J : Ino) (ic : Nat) (Q₁ : WalDur → IProp GF) :
    Option (Nat × Nat) → IProp GF
  | none => discP (W := W) dir N h jr ic Q₁
  | some _ => iprop(walUnlockedTokX (W := W) ∗ (∃ d, Q₁ d) ∗ walDirKey (W := W) dir (ic + 1) J walTmps)

/-- **R: `Discard`'s rename's update** (see the file header). The claim `(jr, N, h)` pinned
(`walCleanPin`), holding `nm` (the WAL's directory `J`) and `tmp` (nothing). -/
theorem discAU (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir nm tmp : GoString) (N : NameSet) (h : NamesH) (J : Ino) (lb ic : Nat)
    (Q₁ : WalDur → IProp GF)
    (hin : InArea r dir nm) (hne : nm ≠ tmp) (hnmN : N.Mem nm) (htN : N.Mem tmp)
    (hJ : h.cur !! nm = some (.dir J)) (ht0 : h.cur !! tmp = none) (hlb : h.next ≤ lb)
    (htmp : ¬ walNameOk tmp) (htS : AreaSlot tmp) :
    ⊢ walInv (W := W) C Mr R jr r -∗ discP (W := W) dir N h jr ic Q₁ -∗
      osAUnc (osNames jr N (DFrac.own (1 : Qp).half) h)
        (renDirOut jr J N nm tmp h (DFrac.own (1 : Qp).half) lb) (discQ (W := W) dir N h jr J ic Q₁) := by
  classical
  iintro #Hinv HP
  iapply osAUnc_coiter _ _ _ (discP (W := W) dir N h jr ic Q₁) $$ [] HP
  iintro !> HP
  unfold osAUncPre
  iintro Hnc
  imod walInv_open C Mr R jr r osAuMask walN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  rw [show osAuMask \ (↑walN : CoPset) = walAuMask from rfl]
  icases Hb with ⟨%s, Hb⟩
  unfold discP
  icases HP with ⟨Hpin, Hau⟩
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl0, #Hcm, Hlays, %Hok, %Hco, ⟨%CR, Hcra, %Hcro⟩,
    Htl, %Han, %Hnm, Hpk, ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  icases walCleanPin_lookup CR N h jr $$ Hcra Hpin with ⟨%Hcr, Hcra, Hpin⟩
  have hco := Hcro
  obtain ⟨hc, hcoh, hexcl, honce, -, -⟩ := Hcro cleanKey N h jr Hcr
  obtain ⟨l1, l2, hcl, hl1, hl2⟩ := honce
  subst hcl
  icases (osClaims_split _ _ _ _).1 $$ Hcl0 with ⟨Hl1, Hα, Hl2⟩
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil] at Hacc
  icases Hacc with ⟨%d0, Hab0, Hcla⟩
  imodintro
  isplitl [Hα]
  · iexact Hα
  iframe Hnc
  isplit
  · -- abort
    iintro Hα
    icases Hcla with ⟨Hab, -⟩
    imod Hab $$ Hab0 with Hau
    imod Hcl $$ [Hg Hl1 Hα Hl2 Hlays Hcra Htl Hpk Hdk Hcp Hnms]
    · iexists s
      iexists Ls, l1 ++ (jr, N, h) :: l2, n, F
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
        ipureintro; exact hco
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
    iframe Hpin Hau
  · -- commit
    iintro %o Hβ
    rcases o with _ | ⟨x, st⟩
    · -- no effect: nothing changes, the client's update aborted
      unfold renDirOut
      simp only [logOut, claimOut]
      icases Hβ with ⟨-, Hα⟩
      icases Hcla with ⟨Hab, -⟩
      imod Hab $$ Hab0 with Hau
      imod Hcl $$ [Hg Hl1 Hα Hl2 Hlays Hcra Htl Hpk Hdk Hcp Hnms]
      · iexists s
        iexists Ls, l1 ++ (jr, N, h) :: l2, n, F
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
          ipureintro; exact hco
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
      simp only [discQ, discP]
      isplitl [Hpin]
      · iexact Hpin
      iexact Hau
    · -- the rename logged: the WAL unnamed, the incarnation bumped, `AU₁` committed
      unfold renDirOut
      simp only [logOut, claimOut]
      icases Hβ with ⟨⟨%hls, -⟩, Hα⟩
      imod walCreating_deleteC CR N h jr $$ Hcra Hpin with ⟨%hdel, Hcra, Hu⟩
      -- the client's view: `dir`'s WAL present
      irevert Hab0
      dsimp only [Std.Tele.app]
      iintro Hab0
      unfold walDiskAtI walDirIsI
      icases Hab0 with ⟨%M, %I1, HM, HI1, %HMd, %hI1⟩
      iunfold walGhost at Hg
      icases Hg with ⟨%I, Hg⟩
      -- the five shares of the incarnations
      icases walUnlockedTokX_open $$ Hu with ⟨%I2, HI2, Hu4, Hu⟩
      icases walParked_incE Ls _ F $$ Hpk Hu4 with ⟨%I4, HI4, Hu4, Hpk⟩
      icases walDirKeysAuth_bump K $$ Hdk with ⟨%I3, HI3, Hdk⟩
      have hle := walLeI_unname s I dir
      imod walGhostI_bump s (unnameS s dir) I (<[dir := incOf I dir + 1]> I) I1 I2 I3 I4 M hle
        (walKeysInArea_upd s dir _) (fun _ hn => hn.upd (fun _ => rfl))
        (walLksAuth_mono s (unnameS s dir) (unlMono_upd s dir _ (fun _ => Nat.le_refl _)))
        $$ Hg HM HI1 HI2 HI3 HI4 with ⟨%he, Hg, HM, HI1, HI2, HI3, HI4, -⟩
      obtain ⟨HMs, e1, e2, e3, e4⟩ := he
      subst I1 I2 I3 I4
      obtain ⟨d1, e1, hd01⟩ := (walOptLe_some_iff _ _).1 HMd
      obtain ⟨ds, hsd, hd1s⟩ := (walOptLe_some_iff _ _).1 (e1 ▸ HMs dir)
      ihave Hdk := Hdk $$ %(<[dir := incOf I dir + 1]> I) %(GMap.delete dir K) %(keys_bump I K dir) HI3
      ihave Hpk := Hpk $$ %(<[dir := incOf I dir + 1]> I) HI4
      -- the WAL's directory key at the new incarnation (its layout's directory, `J`)
      obtain ⟨lay, nm', -, hl, hin0, -, hnm', -⟩ := Hok.1 dir ds hsd
      have hlj : lay.j = J := by
        have e : lay.nm = nm := hnm'.trans (inArea_nm_inj (by rw [Har]; exact hin) hin0)
        rcases HAt.at hl hc (by rw [e]; exact hnmN) with h1 | h1 <;> rw [e, hJ] at h1
        · cases h1; rfl
        · cases h1
      iunfold walIncQ at HI2
      imod walDirKey_insertG (GMap.delete dir K) dir lay.j walTmps (1 : Qp).half.half
        (<[dir := incOf I dir + 1]> I) (GMap.lookup_delete_eq _ _) rfl $$ Hdk HI2 with ⟨Hdk, Hkey, HI2⟩
      -- `AU₁` committed
      icases Hcla with ⟨-, Hco⟩
      isimp only [tforall_nil, Std.Tele.app, ULift.down] at Hco
      have hws : (unnameS s dir).wal = <[dir := { ds with named := false }]> s.wal := unnameS_wal hsd
      imod Hco $$ [HM HI1] with HQ
      · iexists (unnameS s dir).wal, <[dir := incOf I dir + 1]> I
        iframe HM HI1
        ipureintro
        refine ⟨?_, ?_⟩
        · rw [hws, GMap.lookup_insert_eq]
          exact walDurLe_unname (walDurLe_trans hd01 hd1s)
        · rw [incOf_bump]; simp [hI1]
      -- the claims logged, the invariant at the unnamed state
      have hin' : InArea s.area dir nm := by rw [Har]; exact hin
      have hin'' : InArea (unnameS s dir).area dir nm := by rw [unnameS_area]; exact hin'
      have hpres : (unnameS s dir).wal !! dir ≠ none := by rw [hws, GMap.lookup_insert_eq]; simp
      have hun : ∀ d, (unnameS s dir).wal !! dir = some d → d.named = false := by
        intro d hd; rw [hws, GMap.lookup_insert_eq] at hd; cases hd; rfl
      have hent : renDirEnt jr nm tmp J = movEnt jr J nm tmp h := by
        funext st'; unfold movEnt renDirEntA renDirEnt; rw [ht0]
      have H : MovedHyp (l1 ++ (jr, N, h) :: l2) jr N h st nm tmp J :=
        ⟨hc, hcoh, Nat.le_trans hlb hls,
          fun c' hc' hne' hj => ⟨hexcl c' hc' hne' hj nm hnmN, hexcl c' hc' hne' hj tmp htN⟩,
          hne, hnmN, htN, hJ⟩
      have hmv : movClaims (l1 ++ (jr, N, h) :: l2) jr N h x st nm tmp J =
          l1 ++ (jr, N, h.log x (movEnt jr J nm tmp h st) (movCur N h nm tmp J)) :: l2 := by
        unfold movClaims; exact replClaim_split hl1 hl2
      have hnW : ∀ c : Claim, c.1 = jr → ¬ WalDirClaimOf Ls c := fun c hc' => HAt.not_walDirClaimOf c hc'
      have hf := filter_replClaim (fun c : Claim => decide (c.1 ≠ jr)) (c0 := (jr, N, h))
        (c1 := (jr, N, h.log x (movEnt jr J nm tmp h st) (movCur N h nm tmp J))) (by simp) (by simp)
        (l1 ++ (jr, N, h) :: l2)
      ihave Hpk := walParked_cover Ls jr _ _ hnW hf $$ Hpk
      have hok1 := walsOk_unname Hok dir
      have hdk1 := dirKeysOk_unname (K' := GMap.delete dir K) Hdko dir (fun d x hx => by
        by_cases e : d = dir
        · subst e; rw [GMap.lookup_delete_eq] at hx; cases hx
        · rwa [GMap.lookup_delete_ne _ (Ne.symm e)] at hx)
      have han1 := absentNone_unname Han.1 dir
      have hav1 : DirsAvoid R jr (unnameS s dir) := by
        intro dd hdd; rw [unnameS_dirs] at hdd; exact Han.2 dd hdd
      imod Hcl $$ [Hg Hl1 Hα Hl2 Hlays Hcra Htl Hpk Hdk Hcp Hnms]
      · iexists unnameS s dir
        iexists Ls, movClaims (l1 ++ (jr, N, h) :: l2) jr N h x st nm tmp J, n, F
        unfold movClaims
        iframe Hcm Hlays Hpk
        rw [← movClaims]
        isplitl [Hg]
        · iapply walGhostI_ghost; iexact Hg
        isplitr
        · ipureintro; rw [unnameS_area]; exact Har
        isplitl [Hl1 Hα Hl2]
        · rw [hmv]
          iapply (osClaims_split _ _ _ _).2
          iframe Hl1 Hl2
          rw [hent]
          dsimp only [movEnt, movCur]
          iexact Hα
        isplitr
        · ipureintro
          exact walsOk_moved H hok1 HAt han1 hav1 hin'' hpres hun htmp htS
        isplitr
        · ipureintro; exact walsCreateOk_moved Hco
        isplitl [Hcra]
        · iexists _
          iframe Hcra
          ipureintro; intro d N' h' J' hl'; rw [hdel] at hl'; simp at hl'
        isplitl [Htl]
        · iapply walTailsRes_mono C Mr s (unnameS s dir) Ls F ?_ ?_ $$ Htl
          · intro dir' d' hd'
            by_cases hdd : dir' = dir
            · subst hdd; rw [hsd] at hd'; cases hd'
              exact ⟨{ ds with named := false }, by rw [hws, GMap.lookup_insert_eq], rfl, rfl⟩
            · refine ⟨d', ?_, rfl, rfl⟩
              rw [hws, GMap.lookup_insert_ne _ _ (Ne.symm hdd)]; exact hd'
          · intro dir' d' hd'
            by_cases hdd : dir' = dir
            · subst hdd; rw [hws, GMap.lookup_insert_eq] at hd'; cases hd'; exact ⟨ds, hsd, rfl, rfl⟩
            · refine ⟨d', ?_, rfl, rfl⟩
              rw [hws, GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hd'; exact hd'
        isplitr
        · ipureintro; exact ⟨absentNone_moved H han1 hin'' hpres htmp, hav1⟩
        isplitr
        · ipureintro; exact walsNamed_moved H HAt Hnm
        isplitl [Hdk Hcp]
        · iexists <[dir := (lay.j, walTmps)]> (GMap.delete dir K), cp
          iframe Hdk Hcp
          ipureintro; exact dirKeysOk_addKey (dirKeysOk_moved H hok1 HAt hin'' hun htmp hdk1) hl
        isplitr
        · ipureintro; exact walsAt_moved hok1 HAt hin'' htmp hne hc
        isplitl [Hnms]
        · iapply walNamesRes_congr R jr r Ls s (unnameS s dir) ?_ $$ Hnms
          intro dir' d' hd' hn'
          by_cases hdd : dir' = dir
          · subst hdd; rw [hws, GMap.lookup_insert_eq] at hd'; cases hd'; cases hn'
          · rw [hws, GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hd'; exact ⟨d', hd', hn'⟩
        ipureintro
        exact ⟨walsBounded_upd Hbd.1 (fun _ => rfl) (fun _ => rfl), Hbd.2.upd⟩
      imodintro
      simp only [discQ]
      isplitl [Hu HI2 Hu4]
      · iapply Hu $$ %(<[dir := incOf I dir + 1]> I) [HI2] Hu4
        unfold walIncQ; iexact HI2
      isplitl [HQ]
      · iexists d0; iexact HQ
      have hk : incOf (<[dir := incOf I dir + 1]> I) dir = ic + 1 := by rw [incOf_bump]; simp [hI1]
      rw [← hlj, ← hk]
      iexact Hkey

end au

end WalFs
end EtcdGrove
end Perennial

end
