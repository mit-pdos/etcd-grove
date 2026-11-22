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
specs no proof discharges yet (the Perennial-gap specs, `proto.UnmarshalWalRecordE`, the hard-state law
pending the user: `WalHsOwn`'s `reset`). The model's other laws are discharged (`walPb_laws`,
`LawsHsMarshal`, `LawsHsPb`: `CloneHsLaw` and `WalHsOwn.unmarshal` over `proto.Clone`'s and
`proto.Unmarshal`'s trust-boundary specs).
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
public import Proof.google_golang_org.protobuf.proto.ClonePb
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DecEnvSupply

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


section open_
variable [GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
  [_root_.Perennial.internal.filepathlite.Assumptions] [_root_.Perennial.io.Assumptions]
  [_root_.Perennial.time.Assumptions] [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
  [go_etcd_io.raft.v3.Assumptions]

/-- **The specs the tester's proof takes that no proof discharges yet** (the tester Link's hypotheses
but the model's laws and `WalDecEnvSupply`, which are proved): the trust-boundary spec of `proto.Unmarshal`
on a WAL record. (`errors.{IsErrno, IsPathErrnoEof, IsPathErrnoNotExist, IsPathErrnoTerm}` and
`WalDecEnvSupply` proved 2026-11-22, `wal-safe-errors`; `stringslite.HasPrefix` Perennial's, proved there,
since the pin 9c3b81f30.) -/
structure TOpen : Prop where
  unmarshalWalRecordE : proto.UnmarshalWalRecordE.spec (GF := GF) (hG := hG)

end open_

section linked
variable [GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [_root_.Perennial.go_uber_org.zap.Assumptions]
    [github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions] [os.Assumptions]
    [os.fileStat.FieldAssumptions] [github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]
    [os.file.FieldAssumptions] [_root_.Perennial.internal.filepathlite.Assumptions]
    [_root_.Perennial.path.filepath.Assumptions] [syscall.Assumptions]
    [go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]
    [go_etcd_io.etcd.server.v3.storage.wal.Assumptions] [go_etcd_io.raft.v3.Assumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.strings.Assumptions]
    [go_etcd_io.etcd.pkg.v3.ioutil.Assumptions] [_root_.Perennial.encoding.binary.Assumptions]
    [_root_.Perennial.bufio.Assumptions] [go_etcd_io.etcd.pkg.v3.crc.Assumptions]
    [hash.crc32.Assumptions] [go_etcd_io.etcd.pkg.v3.pbutil.Assumptions] [go_uber_org.zap.Assumptions]
    [_root_.Perennial.time.Assumptions] [_root_.Perennial.io.Assumptions]
    [_root_.Perennial.internal.stringslite.Assumptions]

/-- **`Main.spec`, linked**: the tester Link's `wp_Main` at the raftpb model (`walRaftP`, `walRaftU`,
`walRaftHsO`), its laws proved, the rest from `TOpen`. -/
theorem tMain_linked (h : TOpen (GF := GF) (hG := hG)) : Main.spec (GF := GF) (hG := hG) :=
  walTester.etcd_wal.wp_Main walRaftP walRaftU walRaftHsO walRaftU_ok walRaftU_snapCoh
    wal_decEnvSupply (walRaftHsO_own proto.UnmarshalPb.wp_proof)
    (walRaftHsO_own proto.UnmarshalPb.wp_proof)
    (walRaftP_cloneHs proto.ClonePb.wp_proof) walPb_laws.getIndex walPb_laws.getTerm walPb_laws.isEmpty walPb_laws.marshalEnt
    (walRaftP_marshalHs proto.MarshalPb.wp_proof) walPb_laws.mustSync walPb_laws.nil walPb_laws.size
    walPb_laws.unmarshalEnt walPb_laws.zero
    h.unmarshalWalRecordE

end linked

section bounded
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- `hG` with the Go local context `lctx` (a closed theorem's hypotheses are stated at the program's). -/
abbrev tHeapAt (hG : HeapGS .hasLC GF) (lctx : GoLocalContext) : HeapGS .hasLC GF :=
  ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩

/-- **The tester's crash safety for executions of fewer than `N ≤ 2 ^ 62` steps along which fewer than
`T` threads are live** (see the file header): from a state whose Go context satisfies the Go semantics
and the packages' assumptions, with no package initialized, the main thread only, the file extension's
state as on disk (`FsInit`), the area and the oracle directory two distinct roots, the first boot's facts
(`tFirst`: no WAL in the area, no oracle file) and the WAL's paths fitting, every execution with crashes
of `bootWal` returns `#()` if it returns, has no stuck thread and no unrecovered panic. Not the closed
theorem: it takes the initializer's spec (`Hinit_wp`) and the open specs (`TOpen`). -/
theorem etcd_wal_crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics] [go.BasicIntoValInj]
    [_root_.Perennial.go_uber_org.zap.Assumptions]
    [github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions] [os.Assumptions]
    [os.fileStat.FieldAssumptions] [github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]
    [os.file.FieldAssumptions] [_root_.Perennial.internal.filepathlite.Assumptions]
    [_root_.Perennial.path.filepath.Assumptions] [syscall.Assumptions]
    [go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]
    [go_etcd_io.etcd.server.v3.storage.wal.Assumptions] [go_etcd_io.raft.v3.Assumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.strings.Assumptions]
    [go_etcd_io.etcd.pkg.v3.ioutil.Assumptions] [_root_.Perennial.encoding.binary.Assumptions]
    [_root_.Perennial.bufio.Assumptions] [go_etcd_io.etcd.pkg.v3.crc.Assumptions]
    [hash.crc32.Assumptions] [go_etcd_io.etcd.pkg.v3.pbutil.Assumptions] [go_uber_org.zap.Assumptions]
    [_root_.Perennial.time.Assumptions] [_root_.Perennial.io.Assumptions]
    [_root_.Perennial.internal.stringslite.Assumptions] [hPre : GooseGpreS GF] (hAbs : AbsDiskGpreS GF)
    (Hinit_wp : ∀ hG : HeapGS .hasLC GF,
      letI := tHeapAt hG lctx
      {{ ownGoState (hG := (tHeapAt hG lctx).goose_localGS.goose_go_stateGS) ∅ }}
        (App (Val initialize') (Val #()))
      {{ RET #(); isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal }})
    (Hopen : ∀ hG : HeapGS .hasLC GF, TOpen (GF := GF) (hG := tHeapAt hG lctx))
    (N T : Nat) (hN : N ≤ 2 ^ 62) (σ : state) (g : GlobalState) (e : TEnv)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hinit : FsInit (extLocal fsExt σ.world)) (hRe : (extLocal fsExt σ.world).fs.roots = e.R)
    (hr : (e.area, e.jr) ∈ e.R) (ho : (e.orDir, e.jo) ∈ e.R) (hne : e.jo ≠ e.jr)
    (hf : e.orFile.Ok) (hpaths : tWalPathsOk e.area)
    (hfit : PathFits (tWalDir e.area ++ go!".tmp") ∧ PathFits (tWalDir e.area))
    (Hfirst : tFirst e ((extLocal fsExt σ.world).fs.treeDur, []))
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps (bootWal e.area e.orDir) n
      ([bootWal e.area e.orDir], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow (bootWal e.area e.orDir) T n
      ([bootWal e.area e.orDir], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  have hR : RootsOk e.R := hRe ▸ Hinit.2.2.2.1
  refine fsSQ_crash_adequacyShared (GF := GF) tSQ tQ (noIoErr_noMapLockErr_keeps tIo tIo) N T
    (bootWal e.area e.orDir) σ g (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) Hinit
    (fun L V => tGenPre e L V) ?_ ?_ n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · -- the first generation: the tree as on disk
    intro hG _ _ _
    rw [Hpkgs]
    iintro #Hos - Hgs
    imodintro
    unfold tGenPre
    iframe Hgs
    ileft; ipureintro; exact Hfirst
  · -- every generation
    intro hG HN _ Hlctx' V
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    have hrb : ReceiptBoundLe GF (2 ^ 62) := ⟨by rw [HN]; omega⟩
    rw [hRe]
    exact tGen_wp hAbs (tMain_linked (Hopen hG)) (Hinit_wp hG) e hR hr ho hne hf hpaths (tWalFsOk_of e.area hfit)
      hrb V

end bounded

end etcd_wal
end EtcdGrove
end Perennial

end
