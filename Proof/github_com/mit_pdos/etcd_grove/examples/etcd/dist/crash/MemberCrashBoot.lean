/- Lean-first (no Rocq counterpart).

# `EtcdBootC`'s member part (etcd_safe §5.2, S0 statements)

`plans/etcd-safe-restart-design.md` §4.2-4.5. **Statements only** (S0, 2026-11-26): definitions, one law
(`memberFirst_of_share.law`, P3's) and two theorems whose proofs are labeled `sorry`s (`member_crash_boot`, P4's;
`etcdBootCOff_holds`, A's). Nothing here is reached by a result.

* `memberDistFacts c d i` (persistent): what a member's generations take of the start besides `memberGen`: every
  member's peer address set to etcd's peer protocols of the cluster (`peerAddrFactsAt`, `NewServer_dist`'s and
  `NewServerC_dist`'s `Hpeers`) and the member's client address set to serve etcd's table at the cluster's view
  (`etcdAddrAt`, `Serve_dist`'s and `Serve_distR`'s). Global ghost state: every generation has them.
* `memberPcD c d boot i L` (design §4.2's `Pc i L`): `memberPc` at the start's names and the member's data
  directory, with `memberDistFacts`.
* `memberFirst_of_share.law` (P3): the start's share of member `i`, the file extension's start resources of its
  machine and the empty package state give the first generation's `memberPcD`.
* `member_crash_boot` (P4): member `i`'s boot program is safe in every generation from `memberPcD`, over P3's
  `memberGen_boot.law`, `HardStop` at any escrow (`EtcdServer.HardStop.specG`, proved: `wp_proofG`; it replaced
  S0's `memberStop.law`, P5) and the crash law at the keep with the stopped case
  (`memberGenS_crash_law_holds`, P6).
* `EtcdBootCAt P`, `etcdBootCOff_holds` (A): `EtcdBootC` at the deployments of a class, and its proof for the class
  `etcd_safe` closes first: auth off, lease mode `.none`, no compaction mode (the restart specs' scope:
  `NewServer.specC`'s `ρ.rd.kv.cmp = false`, `memberRestartFacts`' lease mode `.none`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.crash.MemberBoot
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MemberDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.BootSkel
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.DeploymentClass

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProgramLogic Robustness Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

/-! ## The member's precondition -/

section facts
variable {GF : BundledGFunctors} [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
  [GoGlobalContext] [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
  [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
  [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
  [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- **What member `i`'s generations take of the start besides `memberGen`** (persistent; see the file header):
`memberShareD`'s address facts. -/
def memberDistFacts (c : ClusterNames) (d : Deployment) (i : Nat) : IProp GF :=
  iprop(peerAddrFactsAt c.γ (cmsD d) ∗
    etcdAddrAt ((d.members.getD i ⟨go!"", go!"", go!""⟩).client) (c.view d.cfg.auth) (d.ids.getD i (W64 0)))

instance memberDistFacts_persistent (c : ClusterNames) (d : Deployment) (i : Nat) :
    Persistent (memberDistFacts (GF := GF) c d i) := by
  unfold memberDistFacts; infer_instance

/-- The member's cluster names (`MemberCl`) from the start's (`ClusterNames`), its peers `ps`, their contexts
and the bootstrap log `boot` (as `memberShareD` reads them). -/
def memberClOf (c : ClusterNames) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) : MemberCl :=
  ⟨c.γ, c.γk, c.issued, c.cnt, c.wn, c.fs, c.gen, ps, ctxs, LogEntry.toEntries boot 0⟩

/-- **The configuration's directories** (what `memberGen` reads of a configuration: `wal.bootRes`'s data and WAL
directories, `memberRestart`'s data directory): member `i`'s data directory `memberDataDir name` and its dedicated
WAL directory, every other field zero. The program's own configuration (`memberCfg`) has the same two fields. -/
def memberDirCfg (dd : GoString) : go_etcd_io.etcd.server.v3.config.ServerConfig :=
  { (zeroValDef : go_etcd_io.etcd.server.v3.config.ServerConfig) with
    DataDir' := dd, DedicatedWALDir' := srvWalDirOf dd }

/-- Member `i`'s cluster names at the deployment's peers and contexts (`memberShareD`'s). -/
abbrev memberClD (c : ClusterNames) (d : Deployment) (boot : List LogEntry) : MemberCl :=
  memberClOf c (distPs d) (distCtxs d) boot

/-- Member `i`'s directories' configuration (`memberDirCfg` at its data directory). -/
abbrev memberCfgD (d : Deployment) (i : Nat) : go_etcd_io.etcd.server.v3.config.ServerConfig :=
  memberDirCfg (memberDataDir (d.members.getD i ⟨go!"", go!"", go!""⟩).name)

/-- Member `i`'s id. -/
abbrev memberIdD (d : Deployment) (i : Nat) : w64 := d.ids.getD i (W64 0)

/-- **Member `i`'s generation `L`, before its boot** (design §4.2's `Pc i L`): `memberPc` at the start's names
`c`, the peers `distPs d`, their contexts `distCtxs d` and the bootstrap log, at member `i`'s id and data
directory, with the start's address facts (`memberDistFacts`). -/
def memberPcD (c : ClusterNames) (d : Deployment) (boot : List LogEntry) (i : Nat) (L : GooseLocalGS GF) :
    IProp GF :=
  iprop(memberPc (memberClD c d boot) (memberCfgD d i) (memberIdD d i) L ∗ memberDistFacts c d i)

end facts

/-! ## The first generation, the member's crash boot, and `EtcdBootC` by class -/

section crash

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem GooseGlobalGS.gooseInvGS etcdFsSemOk

/-- **P3: the first generation from the start's share** (design §4.3, row "start → gen 1"): at the class's lease
mode `.none`, member `i`'s share of the start (`memberShareD`), its machine's file start resources
(`fsStartResG` of a machine with `ServerStart`'s files: the data directory and the WAL area empty) and the empty
package state give the first generation's `memberPcD`: `memberGen`'s first case (`memberFirst`: the slice, and
the WAL area fresh from `walAreasFresh_boot`, `etcdstart/WalAreas.lean:125`) and the address facts.
**Note for P3:** `memberShareD`'s `memberNamesShare` (the lessor's and auth names' slots, which
`NewServer_dist`'s `Hlslot` takes) is dropped here, since `memberFirst` has no row for it: `memberFirst` (or
`memberPcD`) must gain it before P4 can call `NewServer_dist` on a first start, and B4 (a crash inside the
first `NewServer`) must then give it back (see `notes/etcd-dist-restart-axioms.md`, "Design findings"). -/
abbrev memberFirst_of_share.law [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [go_etcd_io.etcd.client.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [G : GooseGlobalGS .hasLC etcdDistGF] [π : NetProtoGS]
    (c : ClusterNames) (d : Deployment) (boot : List LogEntry) (i : Nat) : Prop :=
  ∀ (L : GooseLocalGS etcdDistGF) (m : Member) (σ : state),
    L.goose_go_local_context = lctx → d.members[i]? = some m → ServerStart m σ →
    ⊢ memberShareD c .none d (distPs d) (distCtxs d) boot i -∗
      Net.fsStartResG L (extLocal Fs.fsExt σ.world) -∗
      ownGoState (hG := L.goose_go_stateGS) ∅ ={⊤}=∗
      memberPcD c d boot i L

/-- **P4: member `i`'s machine's crash boot** (S0 stub, `sorry`; design §4.1-4.3): at `EtcdBootC`'s premises, for a
deployment of the first class (auth off, lease mode `.none`, no compaction mode), member `i`'s boot program
`serverProg d i` is safe in every generation (`Net.CrashBootWpGT` at `etcdFsSem`'s crash premise `etcdCQ`, the
issue record's crash rest, the thread bound `etcdThreads`, every receipt bound up to `etcdSteps`) from
`memberPcD`. Over named hypotheses only: P3's boot (`hboot`), `HardStop` at any escrow (`hstop`: the proved
`EtcdServer.HardStop.specG`, used at `True`; the crash-aware shutdown is the crash-aware `run`'s, which
`NewServer`'s and `Start`'s crash forms carry, `notes/etcd-dist-p5s.md`) and the crash law at the keep
with the stopped case (`hcrash`: `memberGenS_crash_law_holds` at `etcdCQ`, whose `hA1` needs the open decision on
`BoltCrashWhole`, crash-left §3), each at the generation's keep pieces `KeepF`, `KeepB`, `KeepBc` (T7's B4, T10's
open and closed backend keeps). The proof follows `server.member_boot_dist` (P0-P2) per generation, with the keep
slot `memberKeepInv` allocated at boot and filled from `NewServer`'s posts, and the stopper (P3′, after the Go
change): `GracefulStop_dist`, then `hstop`. Its axioms: `NewServer_dist` (restated, pending: the notes file),
`NewServerC_dist`, `Serve_dist`, `Serve_distR`, `serve_dist` (pending the Go change), `GracefulStop_dist`,
`PeerServe_dist`, `NewPeerHandler_dist`, `bootstrap.wp_proof_dist`. -/
theorem member_crash_boot [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [server_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]
    [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [log.NewModel] [net.FieldAssumptions]
    (d : Deployment) (Hd : d.WellFormed) (Hcls : d.cfg.auth = false ∧ lmOf d = .none ∧ (cmpOf d).1 = false)
    (boot : List LogEntry) (Hbf : BootFacts d boot) (Henv : EtcdEnv d) (HEnv : EtcdVerifyOff)
    (Hfips : crypto.fips140.GodebugFips140Off)
    (c : ClusterNames) (i : Nat) (m : Member) (hm : d.members[i]? = some m)
    [G : GooseGlobalGS .hasLC etcdDistGF] [π : NetProtoGS]
    (KeepF : GooseLocalGS etcdDistGF → IProp etcdDistGF)
    (KeepB KeepBc : GooseLocalGS etcdDistGF → memberCrash.MemberKN etcdDistGF → IProp etcdDistGF)
    (hboot : ∀ L : GooseLocalGS etcdDistGF, memberGen_boot.law (GF := etcdDistGF) (hG := ⟨G, atCtx L⟩)
      (memberClD c d boot) (memberCfgD d i) (memberIdD d i))
    (hstop : ∀ L : GooseLocalGS etcdDistGF,
      EtcdServer.HardStop.specG (GF := etcdDistGF) (hG := ⟨G, atCtx L⟩))
    (hcrash : memberGen_crash.law (memberClD c d boot) (memberCfgD d i) (memberIdD d i)
      (memberCrash.memberKeepS (memberClD c d boot) (memberCfgD d i) (memberIdD d i) KeepF KeepB KeepBc)
      etcdCQ) :
    letI := etcdNetExtsCrashInterpD4b
    Net.CrashBootWpGT etcdCQ (etcdIdCrashRest idIssue_crash_interp) etcdThreads 0 etcdSteps (serverProg d i)
      (memberPcD (GF := etcdDistGF) c d boot i) := by
  sorry -- S0 stub (P4): see the docstring

/-- **`EtcdBootC` at the well-formed deployments of a class `P`** (as `EtcdBootNCAt`, `TopLevelRobustness.lean`):
`EtcdBootC`'s body with `P d` one more hypothesis. -/
def EtcdBootCAt (P : Deployment → Prop) : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [server_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions] [client_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel] [net.FieldAssumptions]
    (d : Deployment) (_Hd : d.WellFormed) (_HP : P d) (σs σc σn : List state)
    (_Hp : BootPremises d σs σc σn)
    (_Hfips : crypto.fips140.GodebugFips140Off),
    letI := etcdNetExtsCrashInterpD4b
    ∀ [GooseGlobalGS .hasLC etcdDistGF], receiptBound etcdDistGF ≤ etcdSteps →
      ⊢ ([∗list] a ∈ d.addrs, Net.addrUnset a) ={⊤}=∗
        ∃ (Pc : Nat → GooseLocalGS etcdDistGF → IProp etcdDistGF) (Ps : Nat → IProp etcdDistGF),
          ⌜∀ (i : Nat) (m : Expr × state), (servers d σs)[i]? = some m →
            Net.CrashBootWpGT etcdCQ (etcdIdCrashRest idIssue_crash_interp) etcdThreads 0 etcdSteps
              m.1 (Pc i)⌝ ∗
          ⌜∀ (j : Nat) (m : Expr × state), (clients d σc ++ nodeMachines d σn)[j]? = some m →
            Net.DistBootWpSLT etcdThreads 0 etcdSteps m.1 m.2 (Ps j)⌝ ∗
          ([∗list] i ↦ m ∈ servers d σs, ∀ L : GooseLocalGS etcdDistGF,
            ⌜L.goose_go_local_context = lctx⌝ -∗
            ⌜@ThreadGS.threadBound etcdDistGF L.goose_threadGS = etcdThreads⌝ -∗
            Net.fsStartResG L (extLocal Fs.fsExt m.2.world) -∗
            ownGoState (hG := L.goose_go_stateGS) ∅ ={⊤}=∗ Pc i L) ∗
          [∗list] j ↦ _m ∈ clients d σc ++ nodeMachines d σn, Ps j

/-- **A: the first class boots with crashing members** (S0 stub, `sorry`; design §4.5, task A): auth off, lease
mode `.none`, no compaction mode. The start as `etcdBootNCOff_holds`'s (`netProto_alloc`, `etcd_start`), each
member's `Pc i := memberPcD c d boot i` with its first generation by `memberFirst_of_share.law` (P3) and its
generations by `member_crash_boot` (P4, over P3, P5, P6), the stable machines by `orchBoot`/`nodeBoot` as in
`etcdBootNCOff_holds`. The other classes (lease-granting, auth, compaction) stay named hypotheses of the interim
`etcd_safe` (design D4). -/
theorem etcdBootCOff_holds :
    EtcdBootCAt (fun d => d.cfg.auth = false ∧ lmOf d = .none ∧ (cmpOf d).1 = false) := by
  sorry -- S0 stub (A): see the docstring

end crash

end etcd_dist
end EtcdGrove
end Perennial
