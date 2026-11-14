/- Lean-first (no Rocq counterpart).

# `ReadAll`'s directory syncs: the WAL becomes named (F-N4; W3/W5 of `notes/wal-fsext-plan.md`, twenty-fourth session)

`ReadAll`'s `syncDir(filepath.Dir(w.dir))` (F-N4) commits every entry the log had when the program
knew its length. The WAL's name `nm` is registered (`walNamesRes`): its own claim `(jr, .only [nm],
hn)`, fixed for the generation, of which the program borrows a fraction (`ReadAllCommit.lean`,
`walInvBody_nameClaim`). Once the commit bound is past every entry of `hn` (`hn.next ≤ n`, from
`osNames_next` before the syncs), every crash the claims allow leaves `nm` as `hn.cur` has it
(`regionCrashed_coh`, by the claim's coherence `ClaimCoh`), the WAL's directory, so the WAL state takes
the step to `named = true` (`walInvBody_namedBy`, `walInv_namedBy`): `Create`'s `walInvBody_named`
(`CreateNamed.lean`) with the claim's coherence in place of its name's last writer (a registered
claim may have none: a claim split at the generation's start logs nothing).

* `regionCrashed_coh`: a coherent claim all of whose entries are committed decides its names.
* `walsOk_namedBy`, `dirKeysOk_namedBy`: `walsOk_named`/`dirKeysOk_named` over any proof that every
  crash leaves the WAL's name a directory.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateNamedStep

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **A coherent claim whose entries are all committed decides its names** in every crash. -/
theorem regionCrashed_coh {cl : List Claim} {n : Nat} {m' : Tree} {j : Ino} {N : NameSet}
    {h : NamesH} {b : GoString} (hc : (j, N, h) ∈ cl) (hb : N.Mem b) (hcoh : ClaimCoh h j N)
    (hn : h.next ≤ n) (hr : RegionCrashed cl n m') : m'.entry j b = h.cur !! b := by
  obtain ⟨K, -, h2, h3⟩ := hr
  have e1 : m'.entry j b = h.valAfter j K b := h3 _ hc b hb
  rw [e1]
  exact hcoh.2 K (fun xe hxe => h2 _ hc xe.1 xe.2.1 xe.2.2 hxe
    (Nat.lt_of_lt_of_le (hcoh.1 xe hxe) hn)) b hb

/-- **The invariant's pure facts with the WAL in `dir` named** (`walsOk_named` over any proof that
every crash the claims allow with `n` leaves its name a directory). -/
theorem walsOk_namedBy {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n0 n : Nat} (hn : n0 ≤ n)
    (hok : WalsOk C Mr R jr s Ls cl n0) {dir nm : GoString} {d : WalDur}
    (hd : s.wal !! dir = some d) (hin : InArea s.area dir nm)
    (hname : ∀ m', RegionCrashed cl n m' → ∃ J, m'.entry jr nm = some (.dir J)) :
    WalsOk C Mr R jr (setNamed s dir) Ls cl n := by
  have hok' := walsOk_mono hn hok
  have hw : (setNamed s dir).wal = <[dir := { d with named := true }]> s.wal :=
    absDiskUpd_wal s dir _ d hd
  have harea : (setNamed s dir).area = s.area := absDiskUpd_area s dir _
  have hdirs : (setNamed s dir).dirs = s.dirs := by
    unfold setNamed absDiskUpd; rw [hd]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hok'
  refine ⟨fun dir' d' hd' => ?_, fun dir' hn' => h2 dir' ?_, h3, h4, ?_, ?_⟩
  · rw [hw] at hd'
    by_cases he : dir' = dir
    · subst he
      rw [GMap.lookup_insert_eq] at hd'
      cases hd'
      obtain ⟨lay, nm', hj, hlay, hin', hjr, hnm, hcl, ha, -⟩ := h1 dir' d hd
      have hnmeq : nm' = nm := inArea_name hin' hin
      subst hnmeq
      obtain ⟨lay0, nm0, hj0, hlay0, hin0, hjr0, hnm0, -, -, hco⟩ := hok.1 dir' d hd
      rw [hlay] at hlay0; cases hlay0
      refine ⟨lay, nm', hj, hlay, by rw [harea]; exact hin', hjr, hnm, hcl, walAbsD_named true ha, ?_⟩
      refine crashOkW_named hn hco fun m' hr => ?_
      rw [hjr, hnm]; exact hname m' hr
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hd'
      obtain ⟨lay, nm', hj, hlay, hin', rest⟩ := h1 dir' d' hd'
      exact ⟨lay, nm', hj, hlay, by rw [harea]; exact hin', rest⟩
  · rw [hw] at hn'
    by_cases he : dir' = dir
    · subst he; rw [GMap.lookup_insert_eq] at hn'; cases hn'
    · rwa [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hn'
  · intro dir' nm' hin' hn' m' hr J' hJ'
    rw [harea] at hin'
    rw [hw] at hn'
    by_cases he : dir' = dir
    · subst he; rw [GMap.lookup_insert_eq] at hn'; cases hn'
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hn'
      exact h5 dir' nm' hin' hn' m' hr J' hJ'
  · intro dd hdd m' hr
    rw [hdirs] at hdd
    exact h6 dd hdd m' hr

/-- **The directory keys with the WAL in `dir` named** (`dirKeysOk_named` over any proof that every
crash leaves its name a directory). -/
theorem dirKeysOk_namedBy {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n0 n : Nat}
    {K : GMap GoString (Ino × List GoString)} {c : Option GoString} (hn : n0 ≤ n)
    (hok : WalsOk C Mr R jr s Ls cl n0) (hk : DirKeysOk C Mr jr s Ls cl n0 K c)
    {dir nm : GoString} {d : WalDur}
    (hd : s.wal !! dir = some d) (hin : InArea s.area dir nm)
    (hname : ∀ m', RegionCrashed cl n m' → ∃ J, m'.entry jr nm = some (.dir J)) :
    DirKeysOk C Mr jr (setNamed s dir) Ls cl n K c := by
  have hw : (setNamed s dir).wal = <[dir := { d with named := true }]> s.wal :=
    absDiskUpd_wal s dir _ d hd
  refine ⟨hk.1, fun dir' d' lay hd' hl' hcd => ?_, hk.2.2⟩
  rw [hw] at hd'
  by_cases he : dir' = dir
  · subst he
    rw [GMap.lookup_insert_eq] at hd'; cases hd'
    obtain ⟨lay1, nm', hj, hlay, hin', hjr, hnm, -, -, -⟩ := hok.1 dir' d hd
    rw [hl'] at hlay; cases hlay
    have hnmeq : nm' = nm := inArea_name hin' hin
    subst hnmeq
    exact crashOkA_none_named hn (hk.2.1 dir' d lay hd hl' hcd) fun m' hr => by
      rw [hjr, hnm]; exact hname m' hr
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hd'
    exact crashOkA_mono hn (hk.2.1 dir' d' lay hd' hl' hcd)

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The WAL becomes named, by a committed coherent claim** (see the file header): the invariant's
contents at `s` (the WAL in `dir = r/nm` present), the program's claim (a fraction) on names `N ∋ nm`,
coherent, holding the WAL's directory `J` at `nm`, and a commit bound past its entries: the contents
at `setNamed s dir`, and `walNamed dir`. -/
theorem walInvBody_namedBy (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir nm : GoString) (d : WalDur) (N : NameSet) (dq : DFrac) (h : NamesH)
    (J : Ino) (n : Nat) {Em : CoPset}
    (hd : s.wal !! dir = some d) (hin : InArea r dir nm) (hN : N.Mem nm) (hcoh : ClaimCoh h jr N)
    (hnx : h.next ≤ n) (hJ : h.cur !! nm = some (.dir J)) (hE : ↑osShN ⊆ Em) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ osSharedInv (L := L) R -∗
      osNames (L := L) jr N dq h -∗ osCommitLb (L := L) n ={Em}=∗
      walInvBody (L := L) (W := W) C Mr R jr r (setNamed s dir) ∗ osNames (L := L) jr N dq h ∗
        walNamed (W := W) dir := by
  iintro Hb #Hsh Hn #Hc
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n0, %F, Hg, %Har, Hcl, #Hcm, Hlays, %Hok, %Hco, Hcr, Htl, %Han, %Hnm, Hpk,
    ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  obtain ⟨N', h', hc', hN'⟩ := Hco nm hin.1
  have hmem : ((jr, N', h'), DFrac.own (1 : Qp).half) ∈
      cl.map (fun c => (c, DFrac.own (1 : Qp).half)) := List.mem_map_of_mem hc'
  unfold osClaims
  icases (BigSepL.bigSepL_mem_acc hmem) $$ Hcl with ⟨Hi, Hcl⟩
  imod osNames_same_name R jr N N' dq _ h h' nm hN hN' hE $$ Hsh Hn Hi with ⟨%Hk, Hn, Hi⟩
  obtain ⟨rfl, rfl⟩ := Hk
  ihave Hcl := Hcl $$ Hi
  have hin' : InArea s.area dir nm := by rw [Har]; exact hin
  have hname : ∀ m', RegionCrashed cl (max n0 n) m' → ∃ J', m'.entry jr nm = some (.dir J') :=
    fun m' hr => ⟨J, by
      rw [regionCrashed_coh hc' hN hcoh (Nat.le_trans hnx (Nat.le_max_right _ _)) hr, hJ]⟩
  have hok' := walsOk_namedBy (n := max n0 n) (Nat.le_max_left _ _) Hok hd hin' hname
  have hdn : (setNamed s dir).wal !! dir = some { d with named := true } := by
    rw [show (setNamed s dir).wal = _ from absDiskUpd_wal s dir _ d hd, GMap.lookup_insert_eq]
  imod walGhost_upd_lag (W := W) s (setNamed s dir) (walMapLe_setNamed · s dir)
    (absLe_setNamed s dir) (walKeysInArea_upd s dir _) $$ Hg with ⟨Hg, #Hp⟩
  imodintro
  isplitl [Hg Hcl Hlays Hcr Htl Hpk Hdk Hcp Hnms]
  · iexists Ls, cl, max n0 n, F
    iframe Hg Hcl Hlays
    isplitr
    · ipureintro; rw [show (setNamed s dir).area = s.area from absDiskUpd_area s dir _]; exact Har
    isplitr
    · rcases Nat.le_total n0 n with hle | hle
      · rw [Nat.max_eq_right hle]; iexact Hc
      · rw [Nat.max_eq_left hle]; iexact Hcm
    isplitr
    · ipureintro; exact hok'
    isplitr
    · ipureintro; exact Hco
    iframe Hcr
    isplitl [Htl]
    · iapply walTailsRes_mono C Mr s (setNamed s dir) Ls F ?_ ?_ $$ Htl
      · intro dir' d' hd'
        by_cases hdd : dir' = dir
        · subst hdd; rw [hd] at hd'; cases hd'; exact ⟨_, hdn, rfl, rfl⟩
        · refine ⟨d', ?_, rfl, rfl⟩
          rw [show (setNamed s dir).wal = _ from absDiskUpd_wal s dir _ d hd,
            GMap.lookup_insert_ne _ _ (Ne.symm hdd)]
          exact hd'
      · intro dir' d' hd'
        by_cases hdd : dir' = dir
        · subst hdd; rw [hdn] at hd'; cases hd'; exact ⟨d, hd, rfl, rfl⟩
        · refine ⟨d', ?_, rfl, rfl⟩
          rw [show (setNamed s dir).wal = _ from absDiskUpd_wal s dir _ d hd,
            GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hd'
          exact hd'
    iframe Hpk
    isplitr
    · ipureintro
      refine ⟨absentNone_named (absentNone_mono (Nat.le_max_left _ _) Han.1) dir, fun dd hdd => Han.2 dd ?_⟩
      have hdirs : (setNamed s dir).dirs = s.dirs := by unfold setNamed absDiskUpd; rw [hd]
      rw [← hdirs]; exact hdd
    isplitr
    · ipureintro; exact walsNamed_mono (Nat.le_max_left _ _) Hnm
    isplitl [Hdk Hcp]
    · iexists K, cp
      iframe Hdk Hcp
      ipureintro
      exact dirKeysOk_namedBy (n := max n0 n) (Nat.le_max_left _ _) Hok Hdko hd hin' hname
    iframe Hnms; ipureintro; exact ⟨HAt, walsBounded_upd Hbd (fun _ => rfl) (fun _ => rfl)⟩
  iframe Hn
  unfold walNamed
  iexists (setNamed s dir), { d with named := true }
  iframe Hp
  ipureintro; exact ⟨hdn, rfl⟩

/-- **The WAL becomes named, at a program step** (`walInvBody_namedBy`; the WAL in `dir` known from a
past state). -/
theorem walInv_namedBy (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir nm : GoString) (s0 : AbsDiskState) (d0 : WalDur) (N : NameSet) (dq : DFrac) (h : NamesH)
    (J : Ino) (n : Nat)
    (hd0 : s0.wal !! dir = some d0) (hin : InArea r dir nm) (hN : N.Mem nm) (hcoh : ClaimCoh h jr N)
    (hnx : h.next ≤ n) (hJ : h.cur !! nm = some (.dir J)) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗ walPast (W := W) s0 -∗
      osNames (L := L) jr N dq h -∗ osCommitLb (L := L) n ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ osNames (L := L) jr N dq h ∗ walNamed (W := W) dir := by
  iintro #Hinv #Hsi Hnc #Hp H #Hc
  iapply walInv_stepS C Mr R jr r
    iprop(osSharedInv (L := L) R ∗ walPast (W := W) s0 ∗ osNames (L := L) jr N dq h ∗
      osCommitLb (L := L) n)
    iprop(osNames (L := L) jr N dq h ∗ walNamed (W := W) dir)
    ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb ⟨#Hsi, #Hp, H, #Hc⟩
      iunfold walInvBody at Hb
      icases Hb with ⟨%Ls, %cl, %n0, %F, Hg, Hrest⟩
      icases walPast_ghost_le s s0 $$ Hg Hp with %Hle
      obtain ⟨d, hd, -⟩ := Hle.2.2 dir d0 hd0
      ihave Hb : walInvBody (L := L) (W := W) C Mr R jr r s $$ [Hg Hrest]
      · unfold walInvBody; iexists Ls, cl, n0, F; iframe
      imod walInvBody_namedBy C Mr R jr r s dir nm d N dq h J n hd hin hN hcoh hnx hJ
        walN_osShN_top $$ Hb Hsi H Hc with ⟨Hb, H, #Hnm⟩
      imodintro
      isplitl [Hb]
      · iexists _; iexact Hb
      iframe H Hnm)
    $$ Hinv Hnc [H]
  iframe H; iframe #

end iris

end WalFs
end EtcdGrove
end Perennial

end
