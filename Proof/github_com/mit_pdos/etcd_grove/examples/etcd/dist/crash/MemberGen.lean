/- Lean-first (no Rocq counterpart).

# An etcd member machine's generation (etcd-dist D6, spec phase, 2026-11-24)

`notes/etcd-dist-d6.md`. Statements only: the definitions a member machine's crash proof is written
in, and the statements of the laws the parallel proof tasks deliver (`abbrev <name>.law : Prop`,
proved by `<name>_law_holds` in the task's own file, as `notes/decisions.md`, "Import tiers: a proof
takes a linked lemma as a law"). Model: kvnet's crashing replica (`KvNet/.../kvnet/TopBoot.lean`:
`kvGen`, `kvGen_boot`, `kvGen_crash`, `kvGen_first`; `TopLevelRobustness.lean`: `kvPc`).

* `MemberCl`: the cluster's names a member's generation is stated at (D7's `clusterAllocN` output:
  the server's raft names, the KV names, the request ids' claims' names, the bootstrap peers, contexts
  and log).
* `memberGen C cfg id`: **what a generation of member `id` starts `NewServer(cfg)` from**, at the
  ambient generation (`hG`'s local ghost state): the cluster's persistent facts (D7's `clusterFacts`)
  and either the first start's slice (D7's `memberSlice`, with the WAL area fresh, `wal.bootRes`:
  `NewServer.specG`'s case, `haveWAL` false) or a restart's facts (`memberRestartFacts`, persistent) and
  the image the last crash left (`srvCrashImage`, at the member's raft names with some registry name:
  `NewServer.specC`'s case, `haveWAL` true).
* `memberPc C cfg id L`: the generation `L`'s precondition (`kvPc`'s shape: `memberGen` at `⟨G, L⟩` and
  the empty package state): the `Q` of `crashPre`/`CrashBootWp` for member machines.
* `memberGen_crash.law`: **the crash law** (`kvGen_crash`'s shape): what the server's run keeps for a
  crash (`Keep`, the run's crash invariants: D6.3/D6.4's design), a later credit, the old generation's
  `crashed`, the file extension's crash rest at the crash premise `Q` (which must imply the WAL's `W1`,
  `walInv_crash`'s premise) and the new generation's cells' invariant give the next generation's
  `memberGen`.
* `raftTorn`, `readyCrashTorn.law`: **raft's torn-batch law** (D6.3): a crash in the middle of
  the WAL's `Save` of a batch may keep the first `k` entry records without the state record
  (`walImg`'s second case, `AbsDisk/Impl.lean:115`); with no conf-change entry among them, the id's
  durable state may move to `raftTorn S es k` (the entries appended, term, vote and commits unchanged).
  Without that premise it is false: `issues/raft-commit-lost-with-entries-kept.md`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCrashImage
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AllocN
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Restart
public import GooseLang.Ext.Fs.CrashTok

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- **The cluster's names a member's generation is stated at** (D7's `clusterAllocN`): the server's
raft names `γ` (the cluster's; each member's registry name is its own, `memberGOk`), the KV names
`γk`, the request ids' claims' names, the bootstrap peers `ps` (in `bootstrap`'s order), their
contexts and the bootstrap log `bl`. -/
structure MemberCl [GooseExts] where
  γ : SrvRaft
  γk : KVNames
  issued : GName
  cnt : GName
  wn : GName
  fs : GName
  gen : GName
  ps : List w64
  ctxs : List (List w8)
  bl : List EntryM

section gen
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A member's first generation, before `NewServer`** (D6.1): its slice of the cluster's allocation
(`memberSlice`: its prefix's first key, its node's boot token, durable state `RaftState.init` and
vacancy, its snapshot directory's map, its wait slot, its store's fresh names), at some store index
names, and its WAL area fresh (`wal.bootRes cfg`, from the file extension's start resources: the
`WalAreasInit` start). `memberBoot_of_slice` turns the slice into `NewServer.specG`'s rows. -/
def memberFirst (C : MemberCl) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64) :
    IProp GF :=
  iprop(∃ (x : GName) (γs : srvApi.KVSNames) (cok rev reg : GName),
    etcdstart.memberSlice C.γ C.ps C.ctxs C.bl C.cnt C.wn C.fs C.gen x γs cok rev reg id ∗
    wal.bootRes cfg)

/-- **A member's later generation, before `NewServer`** (D6.1): the restart's persistent facts at the
request names `ρo` of the incarnation that wrote the files (`memberRestartFacts`: the server's raft
log invariant, the claims, the prefix's generators' facts `idPfxInv`, the mint, the read contexts, the
KV invariant, a registered key of the prefix), and the image the last crash left in the data directory
`dd` (`srvCrashImage`), both at the member's raft names `γ'` (the cluster's with some registry name:
open question Q4 of the note). `memberRestartFacts_alloc` (with `idIncarnation_alloc`) gives the new
incarnation's names; `NewServer.specC` takes the rest. -/
def memberRestart (C : MemberCl) (id : w64) (dd : GoString) : IProp GF :=
  iprop(∃ (ρo : ReqNames) (γ' : SrvRaft), ⌜∃ r : GName, γ' = { C.γ with reg := r }⌝ ∗
    etcdstart.memberRestartFacts γ' ρo id ∗ srvCrashImage γ' ρo id dd)

/-- **What a generation of member `id` starts `NewServer(cfg)` from** (D6.1; see the file header):
the cluster's persistent facts, and the first start's slice or a restart's image. The files decide
which (`bootstrap`'s `haveWAL`): a WAL in the member's WAL directory is a restart. -/
def memberGen (C : MemberCl) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64) :
    IProp GF :=
  iprop(etcdstart.clusterFacts C.γ C.γk C.issued C.cnt C.wn C.fs C.gen ∗
    (memberFirst C cfg id ∨ memberRestart C id cfg.DataDir'))

end gen

section pc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [lctx : GoLocalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The generation `L` at the statement's Go context `lctx` (`L` itself when its context is `lctx`,
which `CrashBootWp` assumes of every generation it quantifies over): so that the program's instances
over `lctx` (`go.Semantics`, the packages' `Assumptions`) apply to `memberGen` at the generation. -/
abbrev atCtx (L : GooseLocalGS GF) : GooseLocalGS GF := { L with goose_go_local_context := lctx }

/-- **Member `id`'s generation `L`, before its boot** (`kvPc`'s shape): `memberGen` at the generation
(at the statement's Go context, `atCtx`) and its empty package state. The precondition a member
machine's `CrashBootWp` is stated at (D4c's generalized bridge). -/
def memberPc (C : MemberCl) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64)
    (L : GooseLocalGS GF) : IProp GF :=
  letI : HeapGS .hasLC GF := ⟨G, atCtx L⟩
  iprop(memberGen C cfg id ∗ ownGoState ∅)

end pc

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [lctx : GoLocalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

/-- **The member's crash law** (D6.3/D6.4's deliverable; `kvGen_crash`'s shape): for generations `L`
and `L'` whose Go context is the statement's (`CrashBootWp`'s `lctx`), what the run of `L` keeps for
a crash (`Keep L`: the run's crash invariants and their tokens, e.g. the durability invariant's, the
WAL area's `walInv` with `walCrashTok`, the backend file's, the snapshot directory's, the
`osSharedInv`), a later credit, `L`'s `crashed`, the file extension's crash rest at the crash premise
`Q` and `L'`'s cells' invariant give `L'`'s `memberGen`. `Q` is the bridge's (D4c): `walInv_crash`
needs `Q st st' → W1 walCodec st st'`. -/
abbrev memberGen_crash.law (C : MemberCl) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (id : w64) (Keep : GooseLocalGS GF → IProp GF) (Q : Fs.OsState → Fs.OsState → Prop) : Prop :=
  ∀ (L L' : GooseLocalGS GF) (V' : Fs.Hist),
    L.goose_go_local_context = lctx → L'.goose_go_local_context = lctx →
    letI : HeapGS .hasLC GF := ⟨G, L⟩;
    (⊢ Keep L -∗ £ 1 -∗ crashed (hC := L.goose_crashGS) -∗
      Fs.crashRest Q (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) [] false V' -∗
      Fs.osInv (L := L') ={⊤}=∗
      memberGen (hG := ⟨G, atCtx L'⟩) C cfg id)

end crash

/-! ## Raft's torn batch (D6.3) -/

/-- **The durable state after a torn `Save`** (D6.3): `S` with the first `k` entries of the batch `es`
appended (the WAL's entry records kept, `walImg`'s second case), its term, vote, commit and lowest
commit `wcommit` unchanged (the state record, written last, lost). -/
def raftTorn [GooseExts] (S : RaftState) (es : List EntryM) (k : Nat) : RaftState :=
  { S with ents := appendEnts S.base S.ents (es.take k) }

section torn
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Raft's torn-batch crash law** (D6.3; beside `readyCrashEnter`, which enters the whole batch,
and `nodeCrash`, which discards it): after the crash of the generation that ran node `n`, the crash
token of its arm, with a share of `n`'s liveness, may move the id's durable state from `st.durable`
to `raftTorn st.durable es k` for a batch `es` without a snapshot (`st'.handling`) and any `k`, **when no
entry of the kept prefix is a conf change**, and gives the id's vacancy back. The premise is needed:
with two conf changes in the prefix the law is false (`issues/raft-commit-lost-with-entries-kept.md`:
the restarted node campaigns in its old configuration). It covers every batch of a static cluster but
the first (the bootstrap log, `MemberCl.bl`, `notes/etcd-dist-d6.md` Q1). -/
abbrev readyCrashTorn.law : Prop :=
  ∀ (n : NodeH) (γ : Cluster) (N : Namespace) (id : w64) (st st' : NodeDriverState)
    (ms : List QMsg) (es : List EntryM) (k : Nat) (x : CrashNames) (q : Qp) (E : CoPset),
    ↑N ⊆ E → st'.handling = some (es, none) → (∀ e ∈ es.take k, ¬ IsConfEnt e) →
    ⊢ crashed -∗ nodeCrashTok (GF := GF) γ id x -∗ nodeArm n γ x -∗ nodeRunning n γ N q -∗
      readyEnter n γ N id st st' ms -∗ raftState γ id st.durable ={E}=∗
        raftState γ id (raftTorn st.durable es k) ∗ nodeVacant γ id

end torn

end etcd_dist
end EtcdGrove
end Perennial
