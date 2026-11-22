/- Lean-first (no Rocq counterpart).

# The WAL tester's crash adequacy (U7, step 3 of `notes/wal-units/tester.md`'s handoffs)

The boot program `bootWal area orDir` (initialize the package, then `Main(area, orDir)`) run with crashes
over the Linux file extension, every generation in the shared mode from its start
(`fsSQ_crash_adequacyShared`), under the semantics `tExtsSem`: the file system does not fail (`tSQ`, no
I/O error and no lock or mapping error on any file or path, the etcd examples' `etcdSQ`) and every crash
keeps no CRC collision in the WAL's images (`tQ`, the WAL's `W1`, `walInv_crash`'s premise).

A generation's precondition (`tGenPre`): its package state empty, and either the first boot's facts on
the tree (no WAL, no oracle file) or what the previous generation's crash left (`TCrashed`). Its WP:
`tBoot0`/`tBootCrash` from the shared mode's resources (`osShared`) give `TBoot`, which is the program's
part `TRun` (`Main.spec`'s precondition) and the crash tokens; the crash frame is `tester_crash`.

`etcd_wal_crash_safety_bounded` is not the closed theorem (the user's hard stop): it takes, as
hypotheses, the package initializer's spec (`Hinit_wp`: the initializer registers the WAL's metrics,
whose rights `prometheus.namesFree` only `goose_adequacy_start`, a crash-free adequacy, hands out) and the
specs no proof discharges yet (the Perennial-gap specs, `proto.UnmarshalWalRecordE`, the hard-state laws
pending the user: `CloneHsLaw`, `WalHsOwn`'s `unmarshal` and `reset`). The model's other laws are
discharged (`walPb_laws`, `LawsHsMarshal`).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Link
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Boot0
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Crash
public import GooseLang.Ext.Fs.AdequacyShared
public import GooseLang.Ext.Fs.NoIoErr
public import GooseLang.Ext.Fs.NoMapLockErr
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Laws
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.LawsHsMarshal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3 Fs WalEnc WalFs

attribute [local instance] fsExts fsExtsInterp

/-! ## The semantics -/

/-- **Every file and every path.** -/
def tIo : IoSet := ⟨fun _ _ => True, fun _ => True⟩

/-- **The file system does not fail** (the etcd examples' `etcdSQ`). -/
abbrev tSQ : StepPrem := StepPrem.and (NoIoErr tIo) (NoMapLockErr tIo)

/-- **A crash keeps no CRC collision in the WAL's images** (`W1`, `walInv_crash`'s premise). -/
def tQ : OsState → OsState → Prop := fun st st' => W1 walCodec st st'

/-- The file extension's semantics: steps restricted by `tSQ`, crashes by `tQ`. -/
@[reducible] def tFsSem : ExtSemantics fsExt := fsSemWithS tSQ tQ

/-- The program's semantics. -/
@[reducible] def tExtsSem : GooseSemantics := fsExtsSemanticsWithS tSQ tQ

theorem tFsSemOk : letI := tFsSem; FsSemOk :=
  fsSemWithS_ok tSQ tQ (noIoErr_noMapLockErr_keeps tIo tIo)

theorem tHasFs : letI := tExtsSem; letI := tFsSem; HasExt fsExt := fsExtsWithS_hasFs tSQ tQ

theorem tSat : FsStepSat (NoIoErr tIo) (S := tFsSem) :=
  letI := tFsSem
  haveI : FsStepSat tSQ := fsSemWithS_sat tSQ tQ
  fsStepSat_and_left (NoIoErr tIo) (NoMapLockErr tIo)

theorem tSatL : FsStepSat (NoMapLockErr tIo) (S := tFsSem) :=
  letI := tFsSem
  haveI : FsStepSat tSQ := fsSemWithS_sat tSQ tQ
  fsStepSat_and_right (NoIoErr tIo) (NoMapLockErr tIo)

attribute [local instance] tExtsSem tFsSem tFsSemOk tHasFs tSat tSatL

/-- **The WAL's no-failure premise** (`tWalFsOk`) from the semantics and the paths' fit. -/
theorem tWalFsOk_of (area : GoString)
    (hfit : PathFits (tWalDir area ++ go!".tmp") ∧ PathFits (tWalDir area)) : tWalFsOk area :=
  ⟨fsNoErrOn_of tIo (fun _ _ => trivial) (fun _ _ => trivial), hfit⟩

/-! ## The program and a generation's precondition -/

/-- **The tester's boot program**: initialize the package, then `Main(area, orDir)`. -/
def bootWal [GoGlobalContext] [GoSemanticsFunctions] (area orDir : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.Main)) (Val #area)) (Val #orDir))

/-- **The first boot's facts on the tree**: nothing logged, the area and the oracle directory in the
tree, no WAL name of the area holding anything, neither the oracle file nor its temporary. -/
def tFirst (e : TEnv) (V : Hist) : Prop :=
  V.2 = [] ∧ e.jr ∈ V.now ∧ (∀ b, AreaSlot b → V.now.entry e.jr b = none) ∧ e.jo ∈ V.now ∧
    V.now.entry e.jo e.orFile.b = none ∧ V.now.entry e.jo e.orFile.tb = none

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- **A generation's precondition** (the generation `L`, its tree's history `V`). -/
def tGenPre [G : GooseGlobalGS .hasLC GF] (e : TEnv) (L : GooseLocalGS GF) (V : Hist) : IProp GF :=
  iprop(ownGoState (hG := L.goose_go_stateGS) ∅ ∗ (⌜tFirst e V⌝ ∨ TCrashed (L := L) e V))

end adequacy

section gen
variable [GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- **A generation of the tester** (`fsSQ_crash_adequacyShared`'s `Hwp`, at the area's roots): from the
shared mode's resources and the generation's precondition, the boot (`tBoot0` or `tBootCrash`), the boot
program's WP (`Hinit_wp`, then `Main.spec`), and the crash frame (`tester_crash`). -/
theorem tGen_wp (hAbs : AbsDiskGpreS GF) (wp_Main : Main.spec (GF := GF) (hG := hG))
    (Hinit_wp : {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
        (App (Val initialize') (Val #()))
      {{ RET #(); isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal }})
    (e : TEnv) (hR : RootsOk e.R) (hr : (e.area, e.jr) ∈ e.R) (ho : (e.orDir, e.jo) ∈ e.R)
    (hne : e.jo ≠ e.jr) (hf : e.orFile.Ok) (hpaths : tWalPathsOk e.area) (hfs : tWalFsOk e.area)
    (hrb : ReceiptBoundLe GF (2 ^ 62)) (V : Hist) :
    ⊢ osInv (L := hG.goose_localGS) -∗ tGenPre e hG.goose_localGS V -∗
      osShared (L := hG.goose_localGS) e.R V -∗ threadTok ={⊤}=∗
      WP (bootWal e.area e.orDir) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} ∗
      ∀ (L' : GooseLocalGS GF) (V' : Hist), crashed (hC := hG.goose_localGS.goose_crashGS) -∗
        osInv (L := L') -∗
        crashRest tQ (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) [] false V' -∗
        ownGoState (hG := L'.goose_go_stateGS) ∅ ={⊤}=∗
        ∃ V'' : Hist, osTree (L := L') (DFrac.own 1) e.R V'' ∗ tGenPre e L' V'' := by
  iintro #Hos Hpre Hsh -
  unfold tGenPre
  icases Hpre with ⟨Hgs, Hc⟩
  unfold osShared
  icases Hsh with ⟨#Hsi, #Hab, Hcps, -, Hall⟩
  -- the boot: the first, or after a crash
  ihave Hb : |={⊤}=> TBoot (L := hG.goose_localGS) e $$ [Hc Hcps Hall]
  · icases Hc with (%hfirst | Hc)
    · obtain ⟨hV, hjr, hslots, hjo, hob, hot⟩ := hfirst
      iapply tBoot0 hAbs hG.goose_localGS e V hV hR hr hjr hslots ho hjo hne hob hot hf hrb ⊤
        CoPset.subseteq_top $$ Hos Hsi Hab Hcps Hall
    · iapply tBootCrash hG.goose_localGS e V hR hr ho hne hrb ⊤ CoPset.subseteq_top
        $$ Hc Hos Hsi Hab Hcps Hall
  imod Hb with Hb
  icases (TBoot_run e).1 $$ Hb with ⟨%W, %γ, %o, %od, Hrun, Hwt, Hdt⟩
  ihave ⟨#Hinv, #Hok, #Hdd, #Hdi⟩ : TInv (W := W) e γ ∗ WalFs.walAreaOk (W := W) walCodec walRaftMr e.R e.jr
      (e.area) ∗ WalFs.dirDurable (W := W) (e.area) ∗ DurFs.durInv γ.γd e.orFile $$ [Hrun]
  · unfold TRun
    icases Hrun with ⟨#H1, -, -, #H4, #H5, -, -, #H8, -, -⟩
    iframe #
  imodintro
  isplitl [Hgs Hrun]
  · -- the boot program
    unfold bootWal
    wp_apply Hinit_wp $$ Hgs as #Hpkg
    wp_pures
    wp_apply wp_Main W e γ o od hf hpaths hr hfs $$ [Hrun]
    · iframe
    ipureintro; rfl
  · -- after a crash: the tester's crash obligation
    iintro %L' %V' Hcrd #Hos' Hcr Hgs'
    imod tester_crash hAbs tQ (fun _ _ h => h) hG.goose_localGS L' W e γ V' ho
      $$ Hinv Hok Hdd Hdi Hwt Hdt Hcrd Hcr with ⟨Htree, Hc⟩
    imodintro
    iexists V'
    iframe Htree Hgs'
    iright
    iexact Hc

end gen


end etcd_wal
end EtcdGrove
end Perennial

end
