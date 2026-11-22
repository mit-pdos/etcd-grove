/- Lean-first (no Rocq counterpart).

# leaseexpiryN's closed theorem (`notes/leaseN-plan.md`, 2026-11-16; statement approved by the user, 2026-11-16, via etcd-grove-02)

`etcd_leaseexpiry_safe` (`leaseexpiry/Adequacy.lean`) for `examples/etcd/leaseexpiryN` at any member count
`1 ≤ k ≤ 1000`: the package's initialization followed by `Main(k)` -- `k` etcd members started in process,
each serving its raft handler on its own peer listener and its gRPC API on its client address, a lease
of the minimum TTL granted through a client of every member, and at every member, once its listing no
longer lists the lease granted through it, one more listing, with a panic if it lists the lease --
started from a fresh state (no
package initialized, one thread): for every real execution of `n` steps, the main thread's result, if
it has one, is `#()`, no thread is stuck, and no thread has ended in a panic.

It follows from `etcd_adequate_members` (`etcdstart/AdequacyMembers.lean`) with the read package's two
metric names, the `2k` addresses (`leaseexpiryNAddrs`: the members' peer and client addresses, distinct
loopback literals) and the `k` data directories (`leaseexpiryNDirs`), over putgetN's ghost-state bundle
`putgetNGF`, from `leaseexpiryN`'s `wp_initialize'` (over the program's package table `PkgTable.lean`) and
`etcd_leaseexpiryN.wp_Main` (`MainLinked.lean`).

**Its hypotheses** are putgetN's at this program, the members' ids 15-bit distinct (`leaseIdsApart`: their
lease ids apart; `TestMemberIDs` checks it at the token `leaseexpiryN-1973196` for every `k ≤ 1000`), and
`etcd_leaseexpiry_safe`'s `leasePeersOk` (the peers answer the lease handler's path as etcd's handler does,
or not with `200`; the examples' peers answer `404`). No premise about time.

**Over Linux files** (2026-11-16, the user's decision (A) on `wal-lean`, applied on the merge of `lean`):
the program's extensions are `[idIssueExt, fsExt]` (`lib/etcdstart/FsExts.lean`: the file extension's own
semantics, no premise on the environment), since `fileutil`'s package initializer, which the server's
initialization runs, probes `F_OFD_GETLK` through `syscall.FcntlFlock` over the file extension; the
theorem's one new premise is the file extension's initial state, `Fs.FsInit` (`Hfs`: the files as on
disk, the roots well formed), so it says that the program runs on a real file system. Until then the
extensions were `TrivialExt.lean`'s `[idIssueExt]`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AdequacyMembers
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.PkgTable
public import Proof.runtime.Start
public import Proof.runtime.Threads
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.InitLinked

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

/-- The universal camera at slot 0 (putgetN's, moved here unchanged when putgetN's closed theorem
retired, 2026-11-21). -/
def putgetNGF_allG : AllG putgetNGF := ⟨⟨0, rfl⟩⟩

instance putgetNGF_gooseGpreS : GooseGpreS putgetNGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨putgetNGF_allG⟩, ⟨putgetNGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := putgetNGF_allG

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- **leaseexpiryN is safe** (see the file header): for every member count `1 ≤ k ≤ 1000`, every real
execution of `leaseexpiryNProgram k` from a fresh state with one thread, of `n` steps: if the main thread
has finished, its result is `#()`; no thread is stuck; no thread has ended in a panic. -/
theorem etcd_leaseexpiryN_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putgetNGF, ContextReadErrs (GF := putgetNGF) (hG := heapAtN hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetNGF, ContextErrsClient (GF := putgetNGF) (hG := heapAtN hG lctx))
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)
    (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = k) (Hbf : etcd_putgetN.BootFacts ids ps ctxs boot)
    (Hap : leaseIdsApart ids)
    (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (Hlp : leasePeersOk)
    (HNs : prometheus.namesUnclaimed (leaseexpiryNProgram k) leaseexpiryNNames)
    (HAs : addrsUnclaimed (leaseexpiryNProgram k) (etcd_leaseexpiryN.leaseexpiryNAddrs k))
    (HDs : dataDirsAbsent (leaseexpiryNProgram k) (etcd_leaseexpiryN.leaseexpiryNDirs k))
    (HEnv : verifyEnvOff (leaseexpiryNProgram k))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putgetNGF,
      ⊢ etcd_leaseexpiryN.premises (GF := putgetNGF) (hG := heapAtN hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (etcd_leaseexpiryN.leaseexpiryNDirs k))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow (2 ^ 28) n ([leaseexpiryNProgram k], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 1 ≤ 2 ^ 48) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine etcd_adequate_members_below (GF := putgetNGF) (hmsL := etcd_leaseexpiryN.startAddrs_names_len k) (hbody := rfl) (HWal := HWal) (hn := by omega) (hAsLit := etcd_leaseexpiryN.leaseexpiryNAddrs_lit k hk)
    (HEnv := HEnv) github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.initialize'
    ((@! github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Main) #(W64 (k : Int)))
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) (etcd_leaseexpiryN.leaseexpiryNAddrs k)
    (etcd_leaseexpiryN.leaseexpiryNAddrs_nodup k hk) (etcd_leaseexpiryN.leaseexpiryNDirs k)
    (etcd_leaseexpiryN.leaseexpiryNDirs_nodup k hk) (etcd_leaseexpiryN.startAddrs k) []
    (etcd_leaseexpiryN.leaseexpiryNAddrs_perm k) (etcd_leaseexpiryN.leaseexpiryNDirs_perm k)
    σ g ⟨trivial, trivial, trivial⟩ ⟨trivial, Hfs, trivial⟩ Hlctx Hinit Hthreads HNs HAs HDs
    (2 ^ 28) n κs t2 σ2 Hsteps fun hG HN HT => ?_
  letI : HeapGS .hasLC putgetNGF := heapAtN hG lctx
  haveI := Hctx hG
  haveI := Hcec hG
  unfold progOk
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.getIsPkgInit_wf, ?_⟩
  ihave #Hprem' := Hprem hG
  iintro #Hinit Htok ⟨Hms, -⟩
  unfold etcd_leaseexpiryN.startAddrs
  rw [BigSepL.bigSepL_map]
  have hM := etcd_leaseexpiryN.wp_Main (GF := putgetNGF) k n ids ps ctxs boot hk1 hk Hlen Hbf Hap
    (by rw [HT]; word) (srvLevels_of_max HT) (by rw [HN]; omega) (by rw [HN]; omega)
    (by unfold bootWB backend.wbInit; omega) Haf Hbuq Hrf Hdbo Hlp inferInstance
    EtcdGrove.rpctypesEtcdError_asTarget
  wp_apply hM $$ [Hms Htok]
  · iframe; iframe #
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial
