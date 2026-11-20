/- Lean-first (no Rocq counterpart).

# putget3's closed theorem (D21 stage M5, 2026-10-19)

putget's closed theorem (`putget/Adequacy.lean`) for `examples/etcd/putget3`: the package's
initialization followed by `Main()` -- three etcd members started in process, each serving its raft
handler on its own peer listener, a client connected to the first, a `Put` of `k` with `v`, a `Get`
of `k`, and a panic unless the `Get` returned `v` -- started from a fresh state (no package
initialized, one thread): for every real execution of `n` steps, the main thread's result, if it
has one, is `#()`, no thread is stuck, and no thread has ended in a panic.

It follows from `EtcdGrove.goose_adequacy_start` (through `common/Adequacy.lean`'s `etcd_adequate_members`, which gives `Main` the members' start bundles) with the read package's two metric names and the
four addresses (the three peer addresses and the first member's client address), over the
ghost-state bundle `putget3GF` (putget's), from `putget3`'s `wp_initialize'` (over the program's
package table `PkgTable.lean`) and `putget3_Main` (`Results.lean`).

**Its hypotheses** (D19a; putget's, `notes/decisions.md`, D19r and "D21 M5"):
* pure facts of the program and its environment: `BootFacts id₁ id₂ id₃ ps bootLog` (the member ids,
  the peers `ps` in `bootstrap`'s order, a permutation of them, and the bootstrap log Go computes, the ids' 16 low bits distinct and not `0`),
  `authRecordsFit`, `apply.backendUnderQuota`, `grpcRepliesFit` (the replies' encoded size, `grpc.start`'s, 2026-10-31),
  `storage.diskOk` (D22 S-j2),
  `namesUnclaimed`/`addrsUnclaimed` (D19d), and the execution's length (`n + 2 ≤ 2 ^ 28`,
  which gives the write-back budget `n + 7 ≤ backend.wbInit`);
* the semantics, as putget's;
* triples of functions the program calls, with fresh resources (`etcd_putget3.premises`: `bootstrap`'s
  contract for each member, the raft wrapper's names-only contracts, `Stop` of a started node; until 2026-11-13 also
  `runsNoRequireLeader`), at every ghost-state instance;
* (until 2026-10-20 also putget's two marked hypotheses, `EofFromIoInit` and
  `ClosedchanFromContextInit`, now theorems of `io`'s and `context`'s package facts).

**Over Linux files** (2026-11-15, the user's decision (A) on `wal-lean`): the program's extensions are
`[idIssueExt, fsExt]` (`lib/etcdstart/FsExts.lean`: the file extension's own semantics, no premise on
the environment), since `fileutil`'s package initializer, which the server's initialization runs,
probes `F_OFD_GETLK` through `syscall.FcntlFlock` over the file extension; the theorem's one new
premise is the file extension's initial state, `Fs.FsInit` (`Hfs`: the files as on disk, the roots
well formed), so it says that the program runs on a real file system. Until then the extensions were
`TrivialExt.lean`'s `[idIssueExt]`. (wal-link P2, 2026-11-19) The file extension's semantics excludes I/O errors (`etcdFsSem`, `FsExts.lean`: no
file system call that can succeed fails), and the premise `HWal` (`etcdWalAreasInit`) says that each member's
WAL area (`/tmp/etcd-grove-wal/<name>.etcd`, where its dedicated WAL directory is) is a root of the file
extension, present at start with no WAL in it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AdequacyMembers
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putget3.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putget3.PkgTable
public import Proof.runtime.Start
public import Proof.runtime.Threads
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putget3.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putget3.InitLinked

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr

/-! ## The ghost-state bundle -/

/-- The universal camera at slot 0. -/
def putget3GF_allG : AllG putget3GF := ⟨⟨0, rfl⟩⟩

instance putget3GF_gooseGpreS : GooseGpreS putget3GF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨putget3GF_allG⟩, ⟨putget3GF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := putget3GF_allG

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- **putget3 is safe** (see the file header): every real execution of
`putget3Program` from a fresh state with one thread, of `n` steps: if the main thread has finished,
its result is `#()` (`Main` returned: the `Get` that returned `nil` returned the `Put`'s value); no
thread is stuck; no thread has ended in a panic. -/
theorem etcd_putget3_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.putget3.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putget3GF, ContextReadErrs (GF := putget3GF) (hG := heapAt3 hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putget3GF, ContextErrsClient (GF := putget3GF) (hG := heapAt3 hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_putget3.BootFacts id₁ id₂ id₃ ps ctxs boot)
    (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed putget3Program putget3Names)
    (HAs : addrsUnclaimed putget3Program putget3Addrs)
    -- (2026-11-03, the WAL's API, change 6; sweep repairs 1, W3/W4) the members' data directories,
    -- fresh at start (`dataDirsAbsent`; their distinctness is now `decide`d, no longer a hypothesis)
    (HDs : dataDirsAbsent putget3Program [(memberDataDir etcd_putget3.name₁), (memberDataDir etcd_putget3.name₂), (memberDataDir etcd_putget3.name₃)])
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run
    (HEnv : verifyEnvOff putget3Program)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putget3GF,
      ⊢ etcd_putget3.premises (GF := putget3GF) (hG := heapAt3 hG lctx) n id₁ id₂ id₃ ps ctxs boot)
    (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) [(memberDataDir etcd_putget3.name₁), (memberDataDir etcd_putget3.name₂), (memberDataDir etcd_putget3.name₃)])
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([putget3Program], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine etcd_adequate_members (GF := putget3GF) (hbody := rfl) (HWal := HWal) (hn := by omega) (hAsLit := by decide) (HEnv := HEnv) github_com.mit_pdos.etcd_grove.examples.etcd.putget3.initialize'
    ((@! github_com.mit_pdos.etcd_grove.examples.etcd.putget3.Main) #())
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) putget3Addrs (by decide) [(memberDataDir etcd_putget3.name₁), (memberDataDir etcd_putget3.name₂), (memberDataDir etcd_putget3.name₃)] (by decide)
    -- (hub step 7) the members' start bundles: the three peers, member 1's client; the program's
    -- address list has member 1's client last (a permutation)
    [(etcd_putget3.name₁, ⟨some etcd_putget3.peerAddr₁, some etcd_putget3.clientAddr₁⟩),
      (etcd_putget3.name₂, ⟨some etcd_putget3.peerAddr₂, none⟩),
      (etcd_putget3.name₃, ⟨some etcd_putget3.peerAddr₃, none⟩)] [] (by decide) (List.Perm.refl _)
    σ g ⟨trivial, trivial, trivial⟩ ⟨trivial, Hfs, trivial⟩ Hlctx Hinit Hthreads HNs HAs HDs
    n κs t2 σ2 Hsteps fun hG HN HT => ?_
  letI : HeapGS .hasLC putget3GF := heapAt3 hG lctx
  haveI := Hctx hG
  haveI := Hcec hG
  unfold progOk
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.etcd.putget3.wp_initialize' _ github_com.mit_pdos.etcd_grove.examples.etcd.putget3.getIsPkgInit_wf, ?_⟩
  ihave #Hprem' := Hprem hG
  iintro #Hinit Htok ⟨Hms, -⟩
  icases Hms with ⟨Hs₁, Hs₂, Hs₃, -⟩
  have hM := etcd_putget3.wp_Main (GF := putget3GF) n id₁ id₂ id₃ ps ctxs boot Hbf (by rw [HT]; word) (srvLevels_of_max HT)
    (by rw [HN]; omega) (by rw [HN]; omega) (by unfold bootWB backend.wbInit; omega) Haf Hbuq Hrf Hdbo inferInstance EtcdGrove.rpctypesEtcdError_asTarget
  wp_apply hM $$ [Hs₁ Hs₂ Hs₃ Htok]
  · iframe; iframe #
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial
