/- Lean-first (no Rocq counterpart).

# leaseexpiryN's closed theorem (`notes/leaseN-plan.md`, 2026-11-16; statement approved by the user, 2026-11-16, via etcd-grove-02)

`etcd_leaseexpiry_safe` (`leaseexpiry/Adequacy.lean`) for `examples/etcd/leaseexpiryN` at any `k : w64`
(`Main` returns at once outside `[1, 1000]`, 2026-11-24): the package's initialization followed by `Main(k)` -- `k` etcd members started in process,
each serving its raft handler on its own peer listener and its gRPC API on its client address, a lease
of the minimum TTL granted through a client of every member, and at every member, once its listing no
longer lists the lease granted through it, one more listing, with a panic if it lists the lease --
started from a fresh state (no
package initialized, one thread): for every real execution of `n` steps, the main thread's result, if
it has one, is `#()`, no thread is stuck, and no thread has ended in a panic.

It follows from `etcd_adequate_members` (`etcdstart/AdequacyMembers.lean`) with the registration rights it allocates
(`leaseexpiryN_regQsOk`), the `2k` addresses (`leaseexpiryNAddrs`: the members' peer and client addresses, distinct
loopback literals) and the `k` data directories (`leaseexpiryNDirs`), none outside `[1, 1000]`, over putgetN's ghost-state bundle
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

**Over the net extension** (2026-11-23, etcd-grove#28, `notes/single-process-restore.md`): retired at the
net swap (tag `single-process-final`) and restored under the `_single_process` name over
`[idIssueExt, fsExt, netExt]` (`lib/etcdstart/NetExts.lean`'s `etcdNetExts`): `net.Listen` is the net
extension's since the swap; the addresses' listening tokens come from its start resources
(`leaseexpiryNAddrs_ok`: every port below `32768`), the statement takes `[net.FieldAssumptions]` and the
network's initial state (`Hg : extsInitGlobal g`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AdequacyMembers
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.PkgTable
public import Proof.runtime.Start
public import Proof.runtime.Threads
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NetExts
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

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem etcdFsSemOk etcdFsNoErr

/-! ## The ghost-state bundle -/

/-- The universal camera at slot 0 (putgetN's, moved here unchanged when putgetN's closed theorem
retired, 2026-11-21). -/
def putgetNGF_allG : AllG putgetNGF := ⟨⟨0, rfl⟩⟩

instance putgetNGF_gooseGpreS : GooseGpreS putgetNGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨putgetNGF_allG⟩, ⟨putgetNGF_allG⟩, ⟨putgetNGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := putgetNGF_allG

/-! ## The addresses are valid for the net extension -/

/-- **The program's addresses are valid for the net extension** (`Net.addrOk`, 2026-11-23: the
single-process theorem over `etcdNetExts` takes their listening tokens from the extension's start):
every port is `127.0.0.1:<p>` with `p` below `32768` (`addr_port`), below Linux's ephemeral range
(`addrOk_loopback`). -/
theorem etcd_leaseexpiryN.leaseexpiryNAddrs_ok (k : w64) :
    ∀ a ∈ etcd_leaseexpiryN.leaseexpiryNAddrs k, Net.addrOk a = true := by
  intro a ha
  obtain ⟨b, i, hb, hi, rfl⟩ := etcd_leaseexpiryN.addr_port k a ha
  exact addrOk_loopback _ (by simp [W64]; omega) (by simp [W64]; omega)

/-! ## The closed theorem -/

/-- The IDs the program's packages register (their metric names' label-free descriptor IDs and
`v3rpc`'s server metrics' IDs, in `regQs`' order; computed with xxhash64, and checked by the kernel in
`leaseexpiryN_regQsOk`; prom-registry, route (b), 2026-11-23). -/
def leaseexpiryNRegKeys : List w64 :=
  [0x12ecdedc778f3f77, 0x6ac118629bed5903, 0x4aa04489ac2b734b, 0x4ab58b8498228b63,
   0x31b044d75943f6dd, 0x5a080044ea5fdf1a, 0x958bb1c4f0e3d61, 0xd537c2a29197bfe6,
   0x38df0bda13eced78, 0xc5eca1b74fabe814, 0x714bc8e301bc1919, 0x7c09ff7fdc8bd9e2,
   0xca706d4e58b535eb, 0x7eaca73262315545, 0xcfa3e07e6efd0dda, 0x94a3ca5582a08ac8,
   0xf4dff1e237623d2, 0x9a0496b0ef986279, 0x6c3eea8e7dbd9701, 0x1c4edd07e42b3902,
   0xa41ef058a0a6b2e, 0x1ac7b57ed76461ba, 0xe6d60bdb6ca2ca2f, 0xe233596477e3f822,
   0xf4109d5f6085f482, 0x8d957e41d1d11d17, 0x1f7b18004d0507ca, 0x9e66b7f695a88383,
   0x606eb6c3266940a1, 0xccb7c98c879ff20c, 0xdca4bc9464724b6, 0xce41c40aa2166e13,
   0xe7cd4a7e1ce001f2, 0x6c80ca5a0a06a60f, 0xc415d620f8a840b3, 0xc174f386755af284,
   0x8e2ca5829b1415ca, 0xf76aa9ea6954a561, 0x79460c68f240b0ab, 0x50db1f551c79b595,
   0x84b7397632eb946f, 0x2b3902ff335816f9, 0x6a15a11de7b828c4, 0x342d1ac3e8fccf46,
   0x8652a92ef6ff21a5, 0x79b607416929bc6b, 0xb617c6d2d636f8d3, 0x8cdefdfd7fbe0f89,
   0x4d5dbff2abdff296, 0x2f589e3e7676603c, 0x7d293418f489e89, 0x1cf0310f1f3cbc4d,
   0xaf13cf18762e0410, 0xab20cb33e635a4d3, 0x4ea7aecf35604fe8, 0xdfccb0d5dbf98fee,
   0x1329a594e50076ed, 0xe21d9196734675f, 0x4f14727af435217b, 0x93f9374046090575,
   0x1f18f72ac56b959b, 0xb99f16de319e8327, 0x6f040a217f98b36f, 0x6e59011109180671,
   0x11c28b1620be2404, 0x7454d00abfa5eebd, 0x3990ae2951922721, 0xc6dbc11e1f9070ed,
   0xee70855f50c035a7, 0xe022592a562465ef, 0xc59e341e500edbf0, 0x4ff1a721c3c867d0,
   0xddb5f8a18722005e, 0x37b32b97f7de5f, 0x9c06bb0ca40cbda8, 0x23dbdcaf102f1686,
   0x1de4f1c3b13fe482, 0xe4ccc50c7daf4c9c, 0x9b8a677c6e6c1ef8, 0x7133d22463246355,
   0xaa607cdd4f5c0a9a, 0xb0bfadd1258d120e, 0xe5bc0e939f7dd45d, 0x35c8acd42298ce6b]

/-- **The registering packages' IDs can have their rights** (prom-registry, route (b)): pairwise
distinct, none a built-in's, no name a built-in's. Decided by the kernel once, over the IDs as literals
(`leaseexpiryNRegKeys`; `mvccfull_regQsOk`). -/
theorem leaseexpiryN_regQsOk : prometheus.regQsOk github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.regQs :=
  prometheus.regQsOk_of_keys _ leaseexpiryNRegKeys (by decide +kernel) (by decide +kernel) (by decide +kernel)

section adequacy
variable [go_gctx : GoGlobalContext]

/-- **leaseexpiryN is safe** (see the file header): for every `k` (`Main` returns at once outside `[1, 1000]`), every real
execution of `leaseexpiryNProgram k` from a fresh state with one thread, of `n` steps: if the main thread
has finished, its result is `#()`; no thread is stuck; no thread has ended in a panic. -/
theorem etcd_leaseexpiryN_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel] [_root_.Perennial.net.FieldAssumptions]
    (Hctx : ∀ hG : HeapGS .hasLC putgetNGF, ContextReadErrs (GF := putgetNGF) (hG := heapAtN hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetNGF, ContextErrsClient (GF := putgetNGF) (hG := heapAtN hG lctx))
    (k : w64)
    (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = uint.nat k) (Hbf : etcd_putgetN.BootFacts ids ps ctxs boot)
    (Hap : leaseIdsApart ids)
    (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (Hlp : leasePeersOk)
    (HAs : addrsUnclaimed (leaseexpiryNProgram k) (etcd_leaseexpiryN.leaseexpiryNAddrs k))
    (HDs : dataDirsAbsent (leaseexpiryNProgram k) (etcd_leaseexpiryN.leaseexpiryNDirs k))
    (HEnv : verifyEnvOff (leaseexpiryNProgram k))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putgetNGF,
      ⊢ etcd_leaseexpiryN.premises (GF := putgetNGF) (hG := heapAtN hG lctx) (uint.nat k) n ids ps
        ctxs boot)
    (σ : state) (g : GlobalState) (Hg : extsInitGlobal g)
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
  refine etcd_adequate_members_below (GF := putgetNGF) (hmsL := etcd_leaseexpiryN.startAddrs_names_len k) (hbody := rfl) (HWal := HWal) (hn := by omega) (hAsLit := etcd_leaseexpiryN.leaseexpiryNAddrs_lit k)
    (hAsOk := etcd_leaseexpiryN.leaseexpiryNAddrs_ok k)
    (HEnv := HEnv) github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.initialize'
    ((@! github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Main) #k)
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) (etcd_leaseexpiryN.leaseexpiryNAddrs k)
    (etcd_leaseexpiryN.leaseexpiryNAddrs_nodup k) (etcd_leaseexpiryN.leaseexpiryNDirs k)
    (etcd_leaseexpiryN.leaseexpiryNDirs_nodup k) (etcd_leaseexpiryN.startAddrs k) []
    (etcd_leaseexpiryN.leaseexpiryNAddrs_perm k) (etcd_leaseexpiryN.leaseexpiryNDirs_perm k)
    σ g ⟨trivial, trivial, Hg.2.2.1, trivial⟩ ⟨trivial, Hfs, trivial, trivial⟩ Hlctx Hinit Hthreads github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.regQs leaseexpiryN_regQsOk HAs HDs
    (2 ^ 28) n κs t2 σ2 Hsteps fun hG HN HT => ?_
  intro _
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
  have hM := etcd_leaseexpiryN.wp_Main (GF := putgetNGF) k n ids ps ctxs boot Hlen Hbf Hap
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
