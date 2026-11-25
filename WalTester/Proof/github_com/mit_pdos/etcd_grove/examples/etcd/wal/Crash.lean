/-
Lean-first (no Rocq counterpart).

# The WAL tester's crash over `fsExt` (W4c U5, `notes/wal-fsext-w4c-plan.md`)

`tester_crash`: the tester's crash obligation (`fsSQ_crash_adequacy`'s, at `⊤`), from the old
generation's invariant (`TInv`) and the persistent parts and crash tokens of its `TBoot` (the WAL's
`walAreaOk`, the area's `dirDurable`, durable's `durInv`, `walCrashTok`, `durCrashTok`), the crash's
`crashed` and `crashRest`: the new generation's tree's shared view (`osShared`) and `TCrashed`
(`BootCrash.lean`), which `tBootCrash` turns into the next `TBoot`.

It cannot refute the crash, so it opens `TInv` and closes it again with its contents (as the main
tree's). Inside:

1. **The WAL's crash first** (`walInv_crash`, with no file taken yet): the new WAL names `W'`, the crash
   view, the new generation's start, its tokens, the boot files, the crashed tree well formed
   (`TreeWf`), and the files it took, each named in a directory under the area (`InAreaDir`).
2. **Durable's crash** (`durInv_crash`) with those files: none is at the oracle file's names
   (`durCrash_hD`), since by unique naming such a file would be named in the oracle directory, a
   root, which no entry of the area names (`TreeWf`; `inAreaDir_not_orDir`). It gives the file's
   contents `v` after the crash, `durState`'s `cur` or `alt`, so (`tOracleFile_crash`) the file holds
   the oracle `o`, or the pending one, either accounting for the WAL (`tRelI`, `tRelA`).
3. **The WAL's state across the crash, by phase** (`tWal_crash`, the main tree's case split over the
   `_keep` lemmas of `S/Crash.lean`): after `Create` the accounting candidate's `walSyncedLb` and
   `walNamed` of the old generation give the crashed state (an image at the candidate's mark) and the
   same facts in the new generation (`WalFs.walDiskAt_crash_keep`), so `tRelI` is rebuilt with the same
   candidate (`tCandOk_crash`); before, the WAL is absent or accounted for by the fresh oracle's candidate (`tPreOk_crash`).
   This is how the new generation gets `walSyncedLb`/`walNamed` back: from the crash view, not from
   `walStart`/`walPast`.
4. `crashRest_treeS`: the new generation's `osShared`, from the old generation's `osSharedInv`.

**`BootFo` of the crashed tree** (every WAL directory holds only files) is carried into `TCrashed` for
`walBootCrash`, from `walInv_crash`'s `NoDirX` of every WAL directory and its pipeline names'
no-directory fact (`bootFo_of`). (Until 2026-11-22 its `nm.tmp` parts were a premise, `hfo : BootFoNmTmp`,
which no premise on the initial state could discharge: gone with `Create`'s `tmpAny`, ledger 2026-11-22.)
Premises: W1 of the crash premise `Q` (`walInv_crash`'s `hQ`),
the oracle directory a root (a world premise, U7), the WAL's ghost state's `AbsDiskGpreS`.
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.BootCrash
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.CrashPure
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Crash

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.Std Iris.ProofMode go_etcd_io.raft.v3 Fs WalFs

/-! ## Masks and the crashed tree (pure) -/

theorem sub_top_diff_tN (N : Namespace) (h : (↑tN : CoPset) ## ↑N) :
    (↑N : CoPset) ⊆ (⊤ : CoPset) \ ↑tN :=
  fun p hp => LawfulSet.mem_diff.2 ⟨CoPset.mem_full, fun hn => h p ⟨hn, hp⟩⟩

theorem walN_sub_tN : (↑WalFs.walN : CoPset) ⊆ (⊤ : CoPset) \ ↑tN :=
  sub_top_diff_tN _ (ndot_ne_disjoint nroot (by decide))

theorem osShN_sub_tN : (↑osShN : CoPset) ⊆ (⊤ : CoPset) \ ↑tN :=
  sub_top_diff_tN _ (ndot_ne_disjoint nroot (by decide))

theorem durN_sub_tN : (↑DurFs.durN : CoPset) ⊆ (⊤ : CoPset) \ ↑tN :=
  sub_top_diff_tN _ (ndot_ne_disjoint nroot (by decide))

/-- **A file named in a directory under the area is named outside the oracle directory**: by
unique naming its only location is in a directory an entry of the area names, and the oracle
directory, a root, is named by no entry. -/
theorem inAreaDir_not_orDir {R : Roots} {m : Tree} (hwf : TreeWf R m) {jr jo : Ino} {d : GoString}
    (ho : (d, jo) ∈ R) {i : Ino} (hi : InAreaDir m jr i) :
    ∀ J b, m.entry J b = some (.file i) → J ≠ jo := by
  intro J b hJ hJo
  obtain ⟨J0, b0, a, h0, ha⟩ := hi
  obtain ⟨rfl, -⟩ := hwf.2.2.2.2 _ _ _ _ _ hJ h0
  subst hJo
  exact hwf.2.2.2.1 _ _ _ ha _ ho

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **The WAL directory's state across the crash, by phase**: the old copy kept, and a new one the
oracle `o` still accounts for, in the new generation. -/
theorem tWal_crash (W W' : WalGS GF) (area : GoString) (o : TOracle) (od : Option WalDur) :
    ⊢@{IProp GF} WalFs.walCrashWal W W' -∗ WalFs.walDirIsI (W := W) (tWalDir area) 0 od -∗
      tRelI (W := W) area o od -∗
      WalFs.walDirIsI (W := W) (tWalDir area) 0 od ∗ ∃ od' : Option WalDur,
        WalFs.walDirIsI (W := W') (tWalDir area) 0 od' ∗ tRelI (W := W') area o od' := by
  iintro Hcv Hw #HR
  cases hcr : o.created with
  | true =>
    simp only [tRelI, hcr, ite_true]
    icases HR with ⟨%d, %c, %hdc, #Hsy, #Hnm⟩
    obtain ⟨hod, hcm, hok, hw⟩ := hdc
    subst hod
    have hk := WalFs.walDiskAt_crash_keep W W' (tWalDir area) 0 d (tCandMark o c)
    unfold WalFs.walDiskAtI at hk
    icases hk $$ Hcv Hw Hsy Hnm with ⟨Hw, %I, %k, %hIk, Hw', #Hsy', #Hnm'⟩
    obtain ⟨hI, hk⟩ := hIk
    iframe Hw
    iexists some { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length }
    iframe Hw'
    iexists _, c
    iframe Hsy' Hnm'
    ipureintro; exact ⟨rfl, hcm, tCandOk_crash hok hI hk, hw⟩
  | false =>
    simp only [tRelI, hcr, Bool.false_eq_true, ite_false]
    icases HR with %hpre
    obtain ⟨hfresh, hnone | ⟨d, hod, hd⟩⟩ := hpre
    · subst hnone
      have hk := WalFs.walAbsent_crash_keep W W' (tWalDir area) 0
      unfold WalFs.walAbsentI at hk
      icases hk $$ Hcv Hw with ⟨Hw, Hw'⟩
      iframe Hw
      iexists none
      iframe Hw'
      ipureintro; exact ⟨hfresh, Or.inl rfl⟩
    · subst hod
      have hk := WalFs.walDiskAt_crash_any_keep0 W W' (tWalDir area) 0 d
      unfold WalFs.walDiskAtI WalFs.walAbsentI at hk
      icases hk $$ Hcv Hw with ⟨Hw, Hcr⟩
      iframe Hw
      icases Hcr with (⟨Hw', %-⟩ | ⟨%I, %k, %hIk, Hw'⟩)
      · iexists none
        iframe Hw'
        ipureintro; exact ⟨hfresh, Or.inl rfl⟩
      · obtain ⟨hI, hk⟩ := hIk
        iexists some { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length }
        iframe Hw'
        ipureintro; exact tPreOk_crash hfresh hd hI hk

/-- **The oracle a crash keeps accounts for the WAL**: the file's oracle after the crash is the
oracle or the pending one, whose relations the invariant holds. -/
theorem tRel_crash [W : WalGS GF] (area : GoString) (o o'' : TOracle) (oa : Option TOracle)
    (od : Option WalDur) (h : o'' = o ∨ oa = some o'') :
    ⊢@{IProp GF} tRelI (W := W) area o od -∗ tRelA (W := W) area oa od -∗
      tRelI (W := W) area o'' od := by
  iintro #HR #HA
  rcases h with rfl | rfl
  · iexact HR
  · unfold tRelA; iexact HA

/-- **The tester's crash** (see the file header). -/
theorem tester_crash (hPre : AbsDiskGpreS GF) (Q : OsState → OsState → Prop)
    (hQ : ∀ st st', Q st st' → W1 walCodec st st') (L L' : GooseLocalGS GF) (W : WalGS GF)
    (e : TEnv) (γ : TGS) (V' : Hist) (ho : (e.orDir, e.jo) ∈ e.R) :
    ⊢ TInv (L := L) (W := W) e γ -∗
      WalFs.walAreaOk (L := L) (W := W) walCodec walRaftMr e.R e.jr (e.area) -∗
      WalFs.dirDurable (W := W) (e.area) -∗ DurFs.durInv (L := L) γ.γd e.orFile -∗
      WalFs.walCrashTok (W := W) -∗ DurFs.durCrashTok (GF := GF) γ.γd -∗
      crashed (hC := L.goose_crashGS) -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) [] false V' ={⊤}=∗
      osShared (L := L') e.R V' ∗ TCrashed (L := L') e V' := by
  iintro #Hinv #Hok #Hdd #Hdi Hwt Hdt #Hcrd Hcr
  unfold WalFs.walAreaOk
  icases Hok with ⟨#Hwi, -, #Hsh, -, -⟩
  -- open the tester's invariant (closed again with its contents)
  unfold TInv
  imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hinv with ⟨Hb, Hclose⟩
  icases Hb with >Hb
  unfold TInvBody
  icases Hb with ⟨%s, %o, %oa, %od, Hds, %hof, Ho, Hw, Hgw, #HR, #HA⟩
  -- the WAL's crash, first
  imod walInv_crash walCodec walCodec_ok walRaftMr Q hQ hPre L L' W e.R e.jr (e.area) V' []
    (fun i hi => by cases hi) ((⊤ : CoPset) \ ↑tN) walN_sub_tN osShN_sub_tN $$ Hwi Hcrd Hwt Hsh Hcr
    with ⟨%W', %s', %D', Hcv, %hp, Hst, -, Hu', Hct', Hbf, Hcr⟩
  obtain ⟨hWR', -, -, hbd, hdr, hwf, hfoX, hfoT, hD'⟩ := hp
  -- durable's crash, with the WAL's files (none at the oracle file's names)
  have hD : ∀ i ∈ D' ++ [], ∀ J b, V'.now.entry J b = some (.file i) → J ≠ e.orFile.J :=
    fun i hi => inAreaDir_not_orDir hwf ho (hD' i (by simpa using hi))
  imod DurFs.durInv_crash Q L L' γ.γd e.orFile e.R (D' ++ []) false V' s ((⊤ : CoPset) \ ↑tN)
    durN_sub_tN osShN_sub_tN (DurFs.durCrash_hD _ _ _ hD) $$ Hdi Hcrd Hdt Hds Hsh Hcr
    with ⟨%v, %D'', %hv, Hds, Hdf, Hdtmp, Hcr⟩
  -- the new generation's tree
  imod crashRest_treeS Q L L' _ V' e.R _ osShN_sub_tN $$ Hsh Hcr with ⟨%hV, Htree, -⟩
  -- the oracle the file holds, accounting for the WAL
  obtain ⟨o'', ho'', hof''⟩ := tOracleFile_crash hof v hv.1
  ihave #HR'' := tRel_crash (W := W) e.area o o'' oa od ho'' $$ HR HA
  -- the area's durability, and the WAL's state, in the new generation
  icases WalFs.dirDurable_crash_keep W W' (e.area) $$ Hcv Hdd with ⟨Hcv, #Hdd'⟩
  icases tWal_crash W W' e.area o'' od $$ Hcv Hw HR'' with ⟨Hw, %od', Hw', #HR'⟩
  -- close the old invariant with its contents
  imod Hclose $$ [Hds Ho Hw Hgw] with -
  · inext
    iexists s, o, oa, od
    iframe Hds Ho Hw Hgw HR HA
    ipureintro; exact hof
  imodintro
  iframe Htree
  unfold TCrashed
  iexists W', s', o'', od', v
  iframe Hst Hbf Hu' Hct' Hw' HR' Hdd' Hdf Hdtmp
  ipureintro; exact ⟨hWR', hV, hbd, hdr, hwf, bootFo_of hfoX hfoT, hof''⟩

end crash

end etcd_wal
end EtcdGrove
end Perennial
