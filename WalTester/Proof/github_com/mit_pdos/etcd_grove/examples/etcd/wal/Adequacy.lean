/- Lean-first (no Rocq counterpart).

# The WAL tester's crash adequacy (U7, step 3 of `notes/wal-units/tester.md`'s handoffs)

The boot program `bootWal area orDir` (initialize the package, then `Main(area, orDir)`) run with crashes
over the Linux file extension, every generation with the tree's shared view (`osShared`)
(`fsSQ_crash_adequacy`), under the semantics `tExtsSem`: the file system does not fail (`tSQ`, no
I/O error and no lock or mapping error on any file or path, the etcd examples' `etcdSQ`) and every crash
keeps no CRC collision in the WAL's images (`tQ`, the WAL's `W1`, `walInv_crash`'s premise).

A generation's precondition (`tGen`: the cells' invariant, the tree's shared view `osShared` at some
history `V`, and `tGenPre`): its package state empty, and either the first boot's facts on the tree (no
WAL, no oracle file) or what the previous generation's crash left (`TCrashed`). Its WP:
`tBoot0`/`tBootCrash` from `osShared` give `TBoot`, which is the program's part `TRun` (`Main.spec`'s
precondition) and the crash tokens; the crash frame is `tester_crash`, which builds the next
generation's `osShared` (`crashRest_treeS`, from the old generation's `osSharedInv`).

`etcd_wal_crash_safety_bounded` is not the closed theorem (the user's hard stop): it takes, as a
hypothesis, the spec no proof discharges yet (`TOpen`: `proto.UnmarshalWalRecordE`, whose error post
`proto.UnmarshalPb.spec` does not give). The package initializer is proved (2026-11-24, `wal-open`): each
generation allocates its own registration rights for the WAL's metric IDs (`tRegQsOk`, route (b) of
prom-registry) and runs the generated `wp_initialize'` (`InitLinked.lean`, `PkgTable.lean`). The model's other laws are discharged (`walPb_laws`,
`LawsHsMarshal`, `LawsHsPb`: `CloneHsLaw` and `WalHsOwn.unmarshal` over `proto.Clone`'s and
`proto.Unmarshal`'s trust-boundary specs).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Link
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Boot0
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Crash
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.InitLinked
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.PkgTable
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.TopLevelDefs
public import GooseLang.Ext.Fs.AdequacyS
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

attribute [local instance] tExtsSem tFsSem tFsSemOk tHasFs tSat tSatL

/-- **The WAL's no-failure premise** (`tWalFsOk`) from the semantics and the paths' fit. -/
theorem tWalFsOk_of (area : GoString)
    (hfit : PathFits (tWalDir area ++ go!".tmp") ∧ PathFits (tWalDir area)) : tWalFsOk area :=
  ⟨fsNoErrOn_of tIo (fun _ _ => trivial) (fun _ _ => trivial), hfit⟩

/-! ## The program and a generation's precondition -/

/-- The IDs the program's packages register (the WAL's three metric names' label-free descriptor IDs, in
`regQs`' order; computed with xxhash64, the same as in the etcd examples' lists, and checked by the kernel in
`tRegQsOk`). -/
def tRegKeys : List w64 := [0xb0bfadd1258d120e, 0xe5bc0e939f7dd45d, 0x35c8acd42298ce6b]

/-- **The tester's registering packages' IDs can have their rights** (prom-registry, route (b)): pairwise
distinct, none a built-in's, no name a built-in's. -/
theorem tRegQsOk : prometheus.regQsOk github_com.mit_pdos.etcd_grove.examples.etcd.wal.regQs :=
  prometheus.regQsOk_of_keys _ tRegKeys (by decide +kernel) (by decide +kernel) (by decide +kernel)

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- **A generation's precondition** (the generation `L`, its tree's history `V`). -/
def tGenPre [G : GooseGlobalGS .hasLC GF] (e : TEnv) (L : GooseLocalGS GF) (V : Hist) : IProp GF :=
  iprop(ownGoState (hG := L.goose_go_stateGS) ∅ ∗ (⌜tFirst e V⌝ ∨ TCrashed (L := L) e V))

/-- **A generation's precondition, with the file extension's resources** (`fsSQ_crash_adequacy`'s
`P`): the cells' invariant, the tree's shared view at some history `V` and `tGenPre`. -/
def tGen [G : GooseGlobalGS .hasLC GF] (e : TEnv) (L : GooseLocalGS GF) : IProp GF :=
  iprop(osInv (L := L) ∗ ∃ V : Hist, osShared (L := L) e.R V ∗ tGenPre e L V)

end adequacy

section gen
variable [GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions] [_root_.Perennial.log.NewModel]

/-- **The right to initialize, from the empty package state** (the generation's `ownGoState ∅`). -/
theorem tOwnInitializing_of_empty (getInit : GoString → IProp GF) :
    ownGoState (hG := hG.goose_localGS.goose_go_stateGS) (∅ : GMap GoString Bool) ⊢
      ownInitializing getInit := by
  iintro Hgs
  rw [ownInitializing_unseal]
  unfold ownInitializingDef
  iexists ∅
  iframe Hgs
  imodintro
  iapply BigSepM.bigSepM_empty.2
  itrivial

/-- **A generation of the tester** (`fsSQ_crash_adequacy`'s `Hwp`, at the area's roots): from the
generation's precondition (`tGen`), the boot (`tBoot0` or `tBootCrash`), the boot
program's WP (the package's `wp_initialize'`, from the generation's registration rights, allocated afresh,
`tRegQsOk`; then `Main.spec`), and the crash frame (`tester_crash`). -/
theorem tGen_wp (hAbs : AbsDiskGpreS GF) (wp_Main : Main.spec (GF := GF) (hG := hG))
    (e : TEnv) (hR : RootsOk e.R) (hr : (e.area, e.jr) ∈ e.R) (ho : (e.orDir, e.jo) ∈ e.R)
    (hne : e.jo ≠ e.jr) (hf : e.orFile.Ok) (hpaths : tWalPathsOk e.area) (hfs : tWalFsOk e.area)
    (hrb : ReceiptBoundLe GF (2 ^ 62)) :
    ⊢ tGen e hG.goose_localGS -∗ threadTok ={⊤}=∗
      WP (bootWal e.area e.orDir) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} ∗
      ∀ (L' : GooseLocalGS GF) (V' : Hist), crashed (hC := hG.goose_localGS.goose_crashGS) -∗
        osInv (L := L') -∗
        crashRest tQ (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) [] false V' -∗
        ownGoState (hG := L'.goose_go_stateGS) ∅ -∗ £ 1 ={⊤}=∗ tGen e L' := by
  unfold tGen
  iintro ⟨#Hos, %V, Hsh, Hpre⟩ -
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
  -- (prom-registry, route (b)) the generation's registration rights: a fresh ghost map of its packages' IDs
  imod (prometheus.regKeys_alloc (GF := GF) _ tRegQsOk) with ⟨%γreg, Hregs⟩
  letI : prometheus.PromRegGS GF := ⟨γreg⟩
  ihave Hregs := prometheus.idToks_regsFree (GF := GF) _ $$ Hregs
  ihave Hown := (tOwnInitializing_of_empty
    (github_com.mit_pdos.etcd_grove.examples.etcd.wal.getIsPkgInit (GF := GF))) $$ Hgs
  imodintro
  isplitl [Hown Hregs Hrun]
  · -- the boot program
    unfold bootWal
    wp_apply (github_com.mit_pdos.etcd_grove.examples.etcd.wal.wp_initialize' _
      github_com.mit_pdos.etcd_grove.examples.etcd.wal.getIsPkgInit_wf) $$ [Hown Hregs] as ⟨-, #Hpkg⟩
    · iframe Hown Hregs
    wp_pures
    wp_apply wp_Main W e γ o od hf hpaths hr hfs $$ [Hrun]
    · iframe
    ipureintro; rfl
  · -- after a crash: the tester's crash obligation
    iintro %L' %V' Hcrd #Hos' Hcr Hgs' -
    imod tester_crash hAbs tQ (fun _ _ h => h) hG.goose_localGS L' W e γ V' ho
      $$ Hinv Hok Hdd Hdi Hwt Hdt Hcrd Hcr with ⟨Htree, Hc⟩
    imodintro
    iframe Hos'
    iexists V'
    iunfold osShared at Htree
    iframe Htree Hgs'
    iright
    iexact Hc

end gen


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

/-- **The tester's crash safety for executions of fewer than `N ≤ 2 ^ 62` steps along which fewer than
`T` threads are live** (see the file header): from a state whose Go context satisfies the Go semantics
and the packages' assumptions, with no package initialized, the main thread only, the file extension's
state as on disk (`FsInit`), the area and the oracle directory two distinct roots, the first boot's facts
(`tFirst`: no WAL in the area, no oracle file) and the WAL's paths fitting, every execution with crashes
of `bootWal` returns `#()` if it returns, has no stuck thread and no unrecovered panic. Not the closed
theorem: it takes the open specs (`TOpen`); `log.NewModel` is the semantics assumption raft's initializer
(`log.New`) needs, as in the etcd examples' closed theorems. -/
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
    [_root_.Perennial.internal.stringslite.Assumptions] [_root_.Perennial.log.NewModel]
    [hPre : GooseGpreS GF] (hAbs : AbsDiskGpreS GF)
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
  refine fsSQ_crash_adequacy (GF := GF) tSQ tQ (noIoErr_noMapLockErr_keeps tIo tIo) N T
    (bootWal e.area e.orDir) σ g (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) Hinit
    (fun L => tGen e L) ?_ ?_ n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · -- the first generation: the tree as on disk
    intro hG _ _ _
    rw [Hpkgs, hRe]
    iintro #Hos - Hsh Hgs
    imodintro
    unfold tGen tGenPre
    iframe Hos
    iexists ((extLocal fsExt σ.world).fs.treeDur, [])
    iframe Hsh Hgs
    ileft; ipureintro; exact Hfirst
  · -- every generation
    intro hG HN _ Hlctx'
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    have hrb : ReceiptBoundLe GF (2 ^ 62) := ⟨by rw [HN]; omega⟩
    exact tGen_wp hAbs (tMain_linked (Hopen hG)) e hR hr ho hne hf hpaths (tWalFsOk_of e.area hfit)
      hrb

end bounded

end etcd_wal
end EtcdGrove
end Perennial

end
